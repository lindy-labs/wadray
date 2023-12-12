# WadRay library for Cairo

![tests](https://github.com/lindy-labs/cairo-wadray/actions/workflows/tests.yml/badge.svg)

This library provides a felt-based implementation of arithmetic functions for two types of fixed-point decimal numbers, `Wad` (18 decimals of precision) and `Ray` (27 decimals of decimal numbers), written in Cairo for [StarkNet](https://docs.cairo-lang.org/index.html).

## Overview

This library includes arithmetic, comparison and conversion functions.

### Arithmetic

#### Addition and Subtraction

Both `Wad` and `Ray` implement the `Add`, `AddEq`, `Sub` and `SubEq` traits.

Addition and subtraction can be performed as follows:
- `a + b`
- `a += b`
- `a - b`
- `a -= b`
where both `a` and `b` are of the same type.

#### Multiplication and Division

Both `Wad` and `Ray` implement the `Mul`, `MulEq`, `Div` and `DivEq` traits.

Multiplication and division can be performed as follows:
- `a * b`
- `a *= b`
- `a / b`
- `a /= b`
where both `a` and `b` are of the same type.

There is also a set of functions for operations involving a `Wad` and a `Ray`:
- `wmul_wr`/`wmul_rw`: Multiply a `Wad` value with a `Ray` value, and divide the product by one `Wad` scale to return a `Ray`
- `wdiv_rw`: Scale up a `Ray` value by one `Wad` scale and divide the scaled value by a `Wad` value to return a `Ray`
- `rmul_wr`/`rmul_rw`: Multiply a `Wad` value with a `Ray` value, and divide the product by one `Ray` scale to return a `Wad`
- `rdiv_wr`: Scale up a `Wad` value by one `Ray` scale and divide the scaled value by a `Ray` to return a `Wad`
- `rdiv_ww`: Scale up a `Wad` value by one `Ray` scale and divide the scaled value by a `Wad` to return a `Ray`

For multiplication, the prefixes `w` and `r` denote whether the product is divided (i.e. scaled down) by a `Wad` or `Ray` respectively. For division, the prefixes `w` and `r` denote whether the first operand is multiplied (i.e. scaled up) by a `Wad` or `Ray` before the division respectively.

#### Zero and one values

Both `Wad` and `Ray` implement the `Zeroable` and `Oneable` traits.
- `WadZeroable::zero()`/`RayZeroable::zero()`: Returns the zero value for `Wad` and `Ray` respectively
- `is_zero()`: Returns true if the `Wad` or `Ray` value is zero
- `is_non_zero()` Returns true if the `Wad` or `Ray` value is not zero

#### Bound values

Both `Wad` and `Ray` implement the `BoundedInt` trait.
- `BoundedWad::max()`: Returns the maximum `Wad` value of 2<sup>128</sup> - 1
- `BoundedWad::min()`: Returns the minimum `Wad` value of 0
- `BoundedRay::max()`: Returns the maximum `Ray` value of 2<sup>128</sup> - 1
- `BoundedRay::min()`: Returns the minimum `Ray` value of 0

### Comparisons

Both `Wad` and `Ray` implement the `PartialEq` and `PartialOrd` traits.

Comparison can be performed as follows:
- `a == b`
- `a != b`
- `a > b`
- `a >= b`
- `a < b`
- `a <= b`
where both `a` and `b` are of the same type.

These functions operate on any `ufelt` values in the range [0, 2<sup>125</sup>], including `wad` and `ray`.
- `unsigned_min(a, b)` - Returns the smaller of two values
- `unsigned_max(a, b)` - Returns the larger of two values

### Conversion

The following conversions are supported by implementing the `Into` trait:
- `Ray` -> `Wad`: Divide the `Ray` value by 10<sup>9</sup> and return a `Wad`
- `Wad` -> `felt252`: Convert a `Wad` to a `felt252`
- `Wad` -> `u256`: Convert a `Wad` to a `u256`

The following conversions are supported by implementing the `TryInto` trait:
- `Wad` -> `Option::<Ray>`: Multiply the `Wad` value by 10<sup>9</sup> and return `Option::Some<Ray>` if there is no overflow or `Option::None` otherwise.
- `u256` -> `Option::<Wad>`: Returns `Option::Some<Wad>` if the value is within bounds of `u128` or `Option::None` otherwise.

## Usage

To use this library, include a copy of `wadray.cairo` in your project, and import the library into your Cairo contracts.

For example, assuming you have a `src/utils` folder with `wad_ray.cairo` and you want to import it into a Cairo file within the same folder:

```cairo
use src::utils::wadray::Wad;
use src::utils::wadray;

fn add_wad(a: Wad, b: Wad) -> Wad {
    a + b
}
```

You can also refer to the test file `src/test_wadray.cairo` for another example.

## Development

### Prerequisites

- [Cairo](https://github.com/starkware-libs/cairo)
- [Scarb](https://docs.swmansion.com/scarb)
- [Starknet Foundry](https://github.com/foundry-rs/starknet-foundry)

### Run tests

To run the tests:

```bash
scarb test
```

## Formal Verification
The WadRay library is in the process of being formally verified by the Lindy Labs FV unit.

## Contribute

We welcome contributions of any kind! Please feel free to submit an issue or open a PR if you have a solution to an existing bug.

## License

This library is released under the [MIT License](LICENSE).
