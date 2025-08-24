use std::mem;

#[cfg(feature = "use_16_bit_node_indices")]
pub type NodeIndex = u16;

#[cfg(not(feature = "use_16_bit_node_indices"))]
pub type NodeIndex = u32;

const NUM_TOP_BINS: u32 = 32;
const BINS_PER_LEAF: u32 = 8;
const TOP_BINS_INDEX_SHIFT: u32 = 3;
const LEAF_BINS_INDEX_MASK: u32 = 0x7;
const NUM_LEAF_BINS: u32 = NUM_TOP_BINS * BINS_PER_LEAF;

#[derive(Clone, Copy, Debug)]
pub struct Allocation {
    pub offset: u32,
    pub metadata: NodeIndex,
}

impl Allocation {
    pub const NO_SPACE: u32 = 0xffffffff;
}

pub struct StorageReport {
    pub total_free_space: u32,
    pub largest_free_region: u32,
}

pub struct StorageReportFull {
    pub free_regions: [StorageReportFullRegion; NUM_LEAF_BINS as usize],
}

#[derive(Clone, Copy)]
pub struct StorageReportFullRegion {
    pub size: u32,
    pub count: u32,
}

#[derive(Clone)]
pub struct Allocator {
    size: u32,
    max_allocs: u32,
    free_storage: u32,

    used_bins_top: u32,
    used_bins: [u8; NUM_TOP_BINS as usize],
    bin_indices: [NodeIndex; NUM_LEAF_BINS as usize],

    nodes: Vec<Node>,
    free_nodes: Vec<NodeIndex>,
    free_offset: u32,
}

impl Default for Allocator {
    fn default() -> Self {
        Self {
            size: Default::default(),
            max_allocs: Default::default(),
            free_storage: Default::default(),
            used_bins_top: Default::default(),
            used_bins: Default::default(),
            bin_indices: [0; NUM_LEAF_BINS as usize],
            nodes: Default::default(),
            free_nodes: Default::default(),
            free_offset: Default::default(),
        }
    }
}

#[derive(Clone, Copy, Default)]
struct Node {
    data_offset: u32,
    data_size: u32,
    bin_list_prev: NodeIndex,
    bin_list_next: NodeIndex,
    neighbor_prev: NodeIndex,
    neighbor_next: NodeIndex,
    used: bool,
}

impl Node {
    const UNUSED: NodeIndex = 0xffffffff;
}

impl Allocator {
    pub fn new(size: u32, max_allocs: u32) -> Self {
        if mem::size_of::<NodeIndex>() == 2 {
            assert!(max_allocs <= 65536);
        }
        let mut allocator = Allocator {
            size,
            max_allocs,
            free_storage: 0,
            used_bins_top: 0,
            used_bins: [0; NUM_TOP_BINS as usize],
            bin_indices: [Node::UNUSED; NUM_LEAF_BINS as usize],
            nodes: vec![
                Node {
                    data_offset: 0,
                    data_size: 0,
                    bin_list_prev: Node::UNUSED,
                    bin_list_next: Node::UNUSED,
                    neighbor_prev: Node::UNUSED,
                    neighbor_next: Node::UNUSED,
                    used: false,
                };
                max_allocs as usize
            ],
            free_nodes: vec![0; max_allocs as usize],
            free_offset: 0,
        };
        allocator.reset();
        allocator
    }

    pub fn storage_report(&self) -> StorageReport {
        let mut largest_free_region = 0;

        for node in &self.nodes {
            if !node.used && node.data_size > largest_free_region {
                largest_free_region = node.data_size;
            }
        }

        StorageReport {
            total_free_space: self.free_storage,
            largest_free_region,
        }
    }

    pub fn storage_report_full(&self) -> StorageReportFull {
        let mut free_regions =
            [StorageReportFullRegion { size: 0, count: 0 }; NUM_LEAF_BINS as usize];

        for node in &self.nodes {
            if !node.used {
                let bin_index = small_float::uint_to_float_round_down(node.data_size) as usize;
                free_regions[bin_index].size = node.data_size;
                free_regions[bin_index].count += 1;
            }
        }

        StorageReportFull { free_regions }
    }

    pub fn allocate(&mut self, size: u32) -> Option<Allocation> {
        // Out of allocations.
        if self.free_offset == 0 {
            return None;
        }

        let min_bin_index = small_float::uint_to_float_round_up(size);
        let min_top_bin_index = min_bin_index >> TOP_BINS_INDEX_SHIFT;
        let min_leaf_bin_index = min_bin_index & LEAF_BINS_INDEX_MASK;

        let mut top_bin_index = min_top_bin_index;
        let mut leaf_bin_index = Allocation::NO_SPACE;

        // If top bin exists, scan its leaf bin. This can fail.
        if self.used_bins_top & (1 << top_bin_index) != 0 {
            leaf_bin_index = find_lowest_set_bit_after(
                self.used_bins[top_bin_index as usize] as u32,
                min_leaf_bin_index,
            );
        }

        if leaf_bin_index == Allocation::NO_SPACE {
            top_bin_index = find_lowest_set_bit_after(self.used_bins_top, min_top_bin_index + 1);

            // Out of space
            if top_bin_index == Allocation::NO_SPACE {
                return None;
            }

            // All leaf bins here fit the alloc, since the top bin was rounded up. Start leaf search from bit 0.
            // NOTE: This search can't fail since at least one leaf bit was set because the top bit was set.
            leaf_bin_index = (self.used_bins[top_bin_index as usize]).trailing_zeros();
        }

        let bin_index = (top_bin_index << TOP_BINS_INDEX_SHIFT) | leaf_bin_index;

        // Pop the top node of the bin. Bin top = node.next.
        let node_index = self.bin_indices[bin_index as usize];

        #[allow(unused_assignments)]
        let mut node_total_size = 0;
        {
            let node = &mut self.nodes[node_index as usize];
            node_total_size = node.data_size;
            node.data_size = size;
            node.used = true;
        }

        let node = self.nodes[node_index as usize];
        self.bin_indices[bin_index as usize] = node.bin_list_next;
        if node.bin_list_next != Node::UNUSED {
            self.nodes[node.bin_list_next as usize].bin_list_prev = Node::UNUSED;
        }
        self.free_storage -= node_total_size;
        #[cfg(feature = "debug_offset_alloc")]
        println!(
            "Free storage: {} (-{}) (allocate)",
            self.free_storage, node_total_size
        );

        if self.bin_indices[bin_index as usize] == Node::UNUSED {
            self.used_bins[top_bin_index as usize] &= !(1 << leaf_bin_index);

            if self.used_bins[top_bin_index as usize] == 0 {
                self.used_bins_top &= !(1 << top_bin_index);
            }
        }

        let reminder_size = node_total_size - size;
        if reminder_size > 0 {
            let new_node_index = self.insert_node_into_bin(reminder_size, node.data_offset + size);

            if node.neighbor_next != Node::UNUSED {
                self.nodes[node.neighbor_next as usize].neighbor_prev = new_node_index;
            }
            self.nodes[new_node_index as usize].neighbor_prev = node_index;
            self.nodes[new_node_index as usize].neighbor_next = node.neighbor_next;
            self.nodes[node_index as usize].neighbor_next = new_node_index;
        }

        Some(Allocation {
            offset: node.data_offset,
            metadata: node_index,
        })
    }

    pub fn free(&mut self, allocation: Allocation) {
        assert!(allocation.metadata != Allocation::NO_SPACE);
        if self.nodes.is_empty() {
            return;
        };

        let node_index = allocation.metadata;
        // Node& node = self.nodes[nodeIndex];

        assert!(self.nodes[node_index as usize].used);

        // Merge with neighbors...
        let node_cp = self.nodes[node_index as usize];
        let mut offset = node_cp.data_offset;
        let mut size = node_cp.data_size;

        if (node_cp.neighbor_prev != Node::UNUSED)
            && (self.nodes[node_cp.neighbor_prev as usize].used == false)
        {
            // Previous (contiguous) free node: Change offset to previous node offset. Sum sizes
            let prev_node = self.nodes[node_cp.neighbor_prev as usize];
            offset = prev_node.data_offset;
            size += prev_node.data_size;

            // Remove node from the bin linked list and put it in the freelist
            self.remove_node_from_bin(node_cp.neighbor_prev);

            assert!(prev_node.neighbor_next == node_index);
            self.nodes[node_index as usize].neighbor_prev = prev_node.neighbor_prev;
        }

        if (node_cp.neighbor_next != Node::UNUSED)
            && (self.nodes[node_cp.neighbor_next as usize].used == false)
        {
            // Next (contiguous) free node: Offset remains the same. Sum sizes.
            let next_node = self.nodes[node_cp.neighbor_next as usize];
            size += next_node.data_size;

            // Remove node from the bin linked list and put it in the freelist
            self.remove_node_from_bin(node_cp.neighbor_next);

            assert!(next_node.neighbor_prev == node_index);
            self.nodes[node_index as usize].neighbor_next = next_node.neighbor_next;
        }

        let neighbor_next = self.nodes[node_cp.neighbor_next as usize].neighbor_next;
        let neighbor_prev = self.nodes[node_cp.neighbor_next as usize].neighbor_prev;

        // Insert the removed node to freelist
        #[cfg(feature = "debug_offset_alloc")]
        println!(
            "Putting node {} into freelist[{}] (free)",
            node_index,
            self.free_offset + 1
        );

        self.free_offset += 1;
        self.free_nodes[self.free_offset as usize] = node_index;

        // Insert the (combined) free node to bin
        let combined_node_index = self.insert_node_into_bin(size, offset);

        // Connect neighbors with the new combined node
        if neighbor_next != Node::UNUSED {
            self.nodes[combined_node_index as usize].neighbor_next = neighbor_next;
            self.nodes[neighbor_next as usize].neighbor_prev = combined_node_index;
        }
        if neighbor_prev != Node::UNUSED {
            self.nodes[combined_node_index as usize].neighbor_prev = neighbor_prev;
            self.nodes[neighbor_prev as usize].neighbor_next = combined_node_index;
        }
    }

    fn remove_node_from_bin(&mut self, node_index: NodeIndex) {
        let node_cp = self.nodes[node_index as usize];

        if node_cp.bin_list_prev != Node::UNUSED {
            // Easy case: We have previous node. Just remove this node from the middle of the list.
            self.nodes[node_cp.bin_list_prev as usize].bin_list_next = node_cp.bin_list_next;
            if node_cp.bin_list_next != Node::UNUSED {
                self.nodes[node_cp.bin_list_next as usize].bin_list_prev = node_cp.bin_list_prev;
            }
        } else {
            // Hard case: We are the first node in a bin. Find the bin.

            // Round down to bin index to ensure that bin >= alloc
            let bin_index = small_float::uint_to_float_round_down(node_cp.data_size);

            let top_bin_index = bin_index >> TOP_BINS_INDEX_SHIFT;
            let leaf_bin_index = bin_index & LEAF_BINS_INDEX_MASK;

            self.bin_indices[bin_index as usize] = node_cp.bin_list_next;
            if node_cp.bin_list_next != Node::UNUSED {
                self.nodes[node_cp.bin_list_next as usize].bin_list_prev = Node::UNUSED;
            }

            // Bin empty?
            if self.bin_indices[bin_index as usize] == Node::UNUSED {
                // Remove a leaf bin mask bit
                self.used_bins[top_bin_index as usize] &= !(1 << leaf_bin_index);

                // All leaf bins empty?
                if self.used_bins[top_bin_index as usize] == 0 {
                    // Remove a top bin mask bit
                    self.used_bins_top &= !(1 << top_bin_index);
                }
            }
        }

        #[cfg(feature = "debug_offset_alloc")]
        println!(
            "Putting node {} into freelist[{}] (remove_node_from_bin)",
            node_index,
            self.free_offset + 1
        );

        // Insert the node to freelist
        self.free_offset += 1;
        self.free_nodes[self.free_offset as usize] = node_index;

        self.free_storage -= node_cp.data_size;

        #[cfg(feature = "debug_offset_alloc")]
        println!(
            "Free storage {} (-{}) (remove_node_from_bin)",
            self.free_storage, node_cp.data_size
        );
    }

    pub fn reset(&mut self) {
        self.free_storage = 0;
        self.used_bins_top = 0;
        self.free_offset = self.max_allocs - 1;

        for i in 0..NUM_TOP_BINS {
            self.used_bins[i as usize] = 0;
        }

        for i in 0..NUM_LEAF_BINS {
            self.bin_indices[i as usize] = Node::UNUSED;
        }

        self.nodes.fill(Node {
            data_offset: 0,
            data_size: 0,
            bin_list_prev: Node::UNUSED,
            bin_list_next: Node::UNUSED,
            neighbor_prev: Node::UNUSED,
            neighbor_next: Node::UNUSED,
            used: false,
        });

        // Freelist is a stack. Nodes in inverse order so that [0] pops first.
        for i in 0..self.max_allocs {
            self.free_nodes[i as usize] = self.max_allocs - i - 1;
        }

        // Start state: Whole storage as one big node
        // Algorithm will split remainders and push them back as smaller nodes
        self.insert_node_into_bin(self.size, 0);
    }

    fn insert_node_into_bin(&mut self, size: u32, data_offset: u32) -> NodeIndex {
        // Round down to bin index to ensure that bin >= alloc
        let bin_index = small_float::uint_to_float_round_down(size);
        let top_bin_index = bin_index >> TOP_BINS_INDEX_SHIFT;
        let leaf_bin_index = bin_index & LEAF_BINS_INDEX_MASK;

        // Bin was empty before?
        if self.bin_indices[bin_index as usize] == Node::UNUSED {
            // Set bin mask bits
            self.used_bins[top_bin_index as usize] |= 1 << leaf_bin_index;
            self.used_bins_top |= 1 << top_bin_index;
        }

        // Take a freelist node and insert on top of the bin linked list (next = old top)
        let top_node_index = self.bin_indices[bin_index as usize];
        let node_index = self.free_nodes[self.free_offset as usize];
        self.free_offset -= 1;
        #[cfg(feature = "debug_offset_alloc")]
        println!(
            "Getting node {} from freelist[{}]",
            node_index, self.free_offset
        );

        self.nodes[node_index as usize] = Node {
            data_offset,
            data_size: size,
            bin_list_prev: Node::UNUSED,
            bin_list_next: top_node_index,
            neighbor_prev: Node::UNUSED,
            neighbor_next: Node::UNUSED,
            used: false,
        };
        if top_node_index != Node::UNUSED {
            self.nodes[top_node_index as usize].bin_list_prev = node_index;
        }
        self.bin_indices[bin_index as usize] = node_index;

        self.free_storage += size;

        #[cfg(feature = "debug_offset_alloc")]
        println!(
            "Free storage: {} (+{}) (insert_node_into_bin)",
            self.free_storage, size
        );

        node_index
    }
}

fn find_lowest_set_bit_after(value: u32, start_index: u32) -> u32 {
    for i in start_index..32 {
        if value & (1 << i) != 0 {
            return i;
        }
    }
    Allocation::NO_SPACE
}

mod small_float {
    pub const MANTISSA_BITS: u32 = 3;
    pub const MANTISSA_VALUE: u32 = 1 << MANTISSA_BITS;
    pub const MANTISSA_MASK: u32 = MANTISSA_VALUE - 1;
    pub fn uint_to_float_round_up(size: u32) -> u32 {
        let mut exp = 0;

        #[allow(unused_assignments)]
        let mut mantissa = 0;

        if size < MANTISSA_VALUE {
            mantissa = size;
        } else {
            let leading_zeros = size.leading_zeros();
            let highest_set_bit = 31 - leading_zeros;

            let mantissa_start_bit = highest_set_bit - MANTISSA_BITS;
            exp = mantissa_start_bit + 1;
            mantissa = (size >> mantissa_start_bit) & MANTISSA_MASK;

            let low_bits_mask = (1 << mantissa_start_bit) - 1;

            if size & low_bits_mask != 0 {
                mantissa += 1;
            }
        }

        (exp << MANTISSA_BITS) + mantissa
    }

    pub fn uint_to_float_round_down(size: u32) -> u32 {
        let mut exp = 0;
        #[allow(unused_assignments)]
        let mut mantissa = 0;

        if size < MANTISSA_VALUE {
            mantissa = size;
        } else {
            let leading_zeros = size.leading_zeros();
            let highest_set_bit = 31 - leading_zeros;

            let mantissa_start_bit = highest_set_bit - MANTISSA_BITS;
            exp = mantissa_start_bit + 1;
            mantissa = (size >> mantissa_start_bit) & MANTISSA_MASK;
        }

        (exp << MANTISSA_BITS) | mantissa
    }
}

#[cfg(test)]
mod tests {
    use crate::utils::offset_alloc::*;

    #[test]
    fn test_allocator_creation() {
        let allocator = Allocator::new(1024, 128);
        assert_eq!(allocator.size, 1024);
        assert_eq!(allocator.max_allocs, 128);
    }

    #[test]
    fn test_allocator_reset() {
        let mut allocator = Allocator::new(1024, 128);
        allocator.reset();
        assert_eq!(allocator.free_storage, 1024);
        assert_eq!(allocator.used_bins_top, 256);
    }

    #[test]
    fn test_insert_node_into_bin() {
        let mut allocator = Allocator::new(1024, 128);
        let node_index = allocator.insert_node_into_bin(256, 0);
        assert_ne!(node_index, Node::UNUSED);
        assert_eq!(allocator.nodes[node_index as usize].data_size, 256);
        assert_eq!(allocator.nodes[node_index as usize].data_offset, 0);
    }

    #[test]
    fn test_allocation_no_space() {
        let _allocator = Allocator::new(1024, 2);
        let allocation = Allocation::NO_SPACE;
        assert_eq!(allocation, 0xffffffff);
    }

    #[test]
    fn test_small_float_round_down() {
        let value = small_float::uint_to_float_round_down(100);
        assert!(value > 0);
    }

    #[test]
    fn test_allocate() {
        let mut allocator = Allocator::new(1024, 128);
        let allocation = allocator.allocate(128);
        assert!(allocation.is_some());
        let allocation = allocation.unwrap();
        assert_eq!(allocation.offset, 0);
        assert!(allocator.nodes[allocation.metadata as usize].used);
    }

    #[test]
    fn test_free() {
        let mut allocator = Allocator::new(1024, 128);
        let allocation = allocator.allocate(128).unwrap();
        allocator.free(allocation);
        assert!(!allocator.nodes[allocation.metadata as usize].used);
        assert_eq!(allocator.free_storage, 1024);
    }
}
