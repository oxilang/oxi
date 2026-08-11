# oxic

![CI status](https://github.com/oxilang/oxi/actions/workflows/linux.yml/badge.svg)

> [!WARNING]
> This branch currently contains an in-development, non-functional version of the compiler. For the older, functioning version, use the [legacy branch](https://github.com/oxilang/oxi/tree/legacy).

Compiler for the Oxi programming language.

```rust
import std::print;

pub fn main() void {
    print("Hello world\n");
}
```

## Requirements

**Building:**

- Rust
- LLVM 21.1
- just

**Usage:**

- LLVM 21.1
- Mold/lld/gold/ld

## Installation

```sh
just install
```

## Running tests

```sh
just test
```

## Usage

Run `oxic --help` for more information.

### Compiling

```sh
oxic file.oxi
```

### Standard library

The compiler expects the standard library under `<root>/lib/oxi/` (e.g. `/usr/lib/oxi/` when installed to `/usr/bin/oxic`). The `OXI_LIB_PATH` environment variable can be used to override this.
The standard library is only needed to be available at compile time, the compiler will include the needed functions in the final binary.

## Notes

- The compiler is still in development, expect bugs and missing features.
