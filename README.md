# WadRay library for Cairo

![tests](https://github.com/lindy-labs/cairo-wadray/actions/workflows/tests.yml/badge.svg)

This library provides a felt-based implementation of arithmetic functions for two types of fixed-point decimal numbers, `Wad` (18 decimals of precision) and `Ray` (27 decimals of decimal numbers), written in Cairo for [Starknet](https://docs.cairo-lang.org/index.html).

## Overview

This library includes arithmetic, comparison and conversion functions.

### Arithmetic

#### Addition and Subtraction

Addition and subtraction can be performed via the `Add`, `AddEq`, `Sub` and `SubEq` traits as follows:
- `a + b`
- `a += b`
- `a - b`
- `a -= b`
where both `a` and `b` are of the same type.

#### Multiplication and Division

Multiplication and division can be performed via the the `Mul`, `MulEq`, `Div` and `DivEq` traits as follows:
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

As these are fixed point operations, do take note that there will be a loss of precision.

#### Zero and one values

The following values and functions for both `Wad` and `Ray` are available via the `Zeroable` and `Oneable` traits.
- `WadZeroable::zero()`/`RayZeroable::zero()`: Returns the zero value for `Wad` and `Ray` respectively
- `is_zero()`: Returns true if the `Wad` or `Ray` value is zero
- `is_non_zero()` Returns true if the `Wad` or `Ray` value is not zero
- `WadOneable::one()`/`RayOneable::one()`: Returns the scale value for `Wad` (i.e. one `Wad` scale) and `Ray` (i.e. one `Ray` scale) respectively
- `is_one()`: Returns true if the `Wad` or `Ray` value is one
- `is_non_one()` Returns true if the `Wad` or `Ray` value is not one

#### Bound values

The bound values for both `Wad` and `Ray` can be obtained via the `BoundedInt` trait.
- `BoundedWad::max()`: Returns the maximum `Wad` value of 2<sup>128</sup> - 1
- `BoundedWad::min()`: Returns the minimum `Wad` value of 0
- `BoundedRay::max()`: Returns the maximum `Ray` value of 2<sup>128</sup> - 1
- `BoundedRay::min()`: Returns the minimum `Ray` value of 0

### Comparisons

Comparison for both `Wad` and `Ray` can be performed via the `PartialEq` and `PartialOrd` traits as follows:
- `a == b`
- `a != b`
- `a > b`
- `a >= b`
- `a < b`
- `a <= b`
where both `a` and `b` are of the same type.

### Conversion

The following conversions can be performed via the `Into` trait:
- `Ray` -> `Wad`: Divide the `Ray` value by 10<sup>9</sup> and return a `Wad`
- `Wad` -> `felt252`: Convert a `Wad` to a `felt252`
- `Wad` -> `u256`: Convert a `Wad` to a `u256`

The following conversions can be performed via the `TryInto` trait:
- `Wad` -> `Option::<Ray>`: Multiply the `Wad` value by 10<sup>9</sup> and return `Option::Some<Ray>` if there is no overflow or `Option::None` otherwise.
- `u256` -> `Option::<Wad>`: Returns `Option::Some<Wad>` if the value is within bounds of `u128` or `Option::None` otherwise.

## Usage

To use this library, add the repository as a dependency in your `Scarb.toml`:

```
[dependencies]
wadray = { git = "https://github.com/lindy-labs/cairo-wadray.git" }
```
then add the following line in your `.cairo` file
```cairo
use wadray::wadray::Wad

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
