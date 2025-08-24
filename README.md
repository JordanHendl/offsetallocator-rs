# offsetallocator-rs

A fast **O(1) offset allocator** for Rust, ported from [Sebastian Aaltonen’s OffsetAllocator](https://github.com/sebbbi/OffsetAllocator).

This crate manages **offset ranges inside a fixed-size region** (like GPU heaps or large buffers). It doesn’t touch your resource memory—only tracks what offsets are free/used.

---

## Features

- **O(1) allocate/free** using a two-level bitfield  
- **Low fragmentation** (≤ 12.5% worst-case, ~6% avg) with float-distributed bins  
- **Resource-agnostic**: works with any region you own (bytes, descriptors, array indices)  
- **Deterministic**: predictable, real-time friendly  

---

## Installation

```toml
[dependencies]
offsetallocator = { git = "https://github.com/JordanHendl/offsetallocator-rs" }
```

---

## Example

```rust
use offsetallocator::{Allocator, Allocation};

fn main() {
    let mut alloc = Allocator::new(12_345);

    let a: Allocation = alloc.allocate(1_337).unwrap();
    println!("offset a = {}", a.offset());

    let b = alloc.allocate(123).unwrap();
    println!("offset b = {}", b.offset());

    alloc.free(a);
    alloc.free(b);
}
```

---

## When to use

- Suballocating GPU buffers/heaps  
- Managing descriptor heaps or array-like arenas  
- Cases needing **fast, bounded-time** allocation  

Not a global allocator — this is for **suballocation only**.

---

## License

MIT, same as the original.  

