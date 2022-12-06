# WadRay library for Cairo

![tests](https://github.com/lindy-labs/cairo-wadray/actions/workflows/tests.yml/badge.svg)

This library provides a felt-based implementation of arithmetic functions for two types of fixed-point decimal numbers, `wad` (18 decimals of precision) and `ray` (27 decimals of decimal numbers), written in Cairo for [StarkNet](https://www.cairo-lang.org/docs/).

The library has been extensively tested with Hypothesis. For more details on running the tests, refer to this [section](#run-tests).

The design of this library was originally inspired by Influenceth's [64x61 fixed-point math library](https://github.com/influenceth/cairo-math-64x61).

## Overview

This library includes arithmetic, aggregation, conversion and bounds check functions.

### Arithmetic

#### Addition and Subtraction

These functions operate on both `wad` and `ray`.

- `add(a, b)`: Addition `a` and `b` with a bounds check that the result is within the range [-2<sup>125</sup>, 2<sup>125</sup>]
- `unsigned_add(a, b)`: Unsigned addition of `a` and `b` with a bounds check that the result is within the range [0, 2<sup>125</sup>]
- `sub(a, b)`: Subtraction of `b` from `a` with a bounds check that the result is within the range [-2<sup>125</sup>, 2<sup>125</sup>]
- `unsigned_sub(a, b)`: Unsigned subtraction of `a` and `b` with a bounds check that the result is within the range [0, 2<sup>125</sup>]

#### Multiplication and Division

The prefixes `w` and `r` denotes whether the function operates on `wad` or `ray` respectively.

- `wmul(a, b)`, `rmul(a, b)`: Multiplication of `a` and `b`
- `wsigned_div(a, b)`, `rsigned_div(a, b)`: Signed division of `a` by `b`
- `wunsigned_div(a, b)`, `runsigned_div(a, b)`: Unsigned division of `a` by `b` with a bounds check that the result is within the range [-2<sup>125</sup>, 2<sup>125</sup>]
- `wunsigned_div_unchecked(a, b)`, `runsigned_div_unchecked(a, b)`: Unsigned division of `a` by `b`

### Aggregation

These functions operate on `wad` only.

- `floor(n)` - Round a value down to the nearest `wad`
- `ceil(n)` - Round a value up to the nearest `wad`

These functions operate on any `ufelt` values in the range [0, 2<sup>125</sup>], including `wad` and `ray`.
- `unsigned_min(a, b)` - Returns the smaller of two values
- `unsigned_max(a, b)` - Returns the larger of two values

### Conversion

- `to_uint(n)`: Convert a felt value to `Uint256`
- `from_uint(n)`: Convert a `Uint256` value to felt with a bounds check that the result is within the range [-2<sup>125</sup>, 2<sup>125</sup>]
- `to_wad(n)`: Multiply `n` by 10<sup>18</sup> with a bounds check that the result is within the range [-2<sup>125</sup>, 2<sup>125</sup>]
- `wad_to_ray(n)`: Multiply `n` by 10<sup>9</sup> with a bounds check that the result is within the range [-2<sup>125</sup>, 2<sup>125</sup>]
- `ray_to_wad(n)`: Divide `n` by 10<sup>9</sup>

### Bounds Check

These functions operate on both `wad` and `ray`.

- `assert_result_valid(n)`: Raises an error if `n` is not in the range [-2<sup>125</sup>, 2<sup>125</sup>]
- `assert_result_valid_unsigned(n)`: Raises an error if `n` is not in the range [0, 2<sup>125</sup>]

## Usage

To use this library, include a copy of `wad_ray.cairo` in your project, and import the library into your Cairo contracts.

For example, assuming you have a `contracts/` folder with `wad_ray.cairo` and you want to import it into a Cairo file within the same folder:

```cairo
%lang starknet

from starkware.cairo.common.cairo_builtins import HashBuiltin
from contracts.wad_ray import WadRay

@external
func add_wad{syscall_ptr : felt*, pedersen_ptr : HashBuiltin*, range_check_ptr}(
    a: felt, b: felt
) -> (c: felt) {
    let c: felt = WadRay.add(a, b);
    return (c,);
}
```

You can also refer to the test file `tests/test_wad_ray.cairo` for another example.

## Development

### Set up the project

Clone the repository

```bash
git clone git@github.com:lindy-labs/cairo-wadray.git
```

`cd` into it and create a Python virtual environment:

```bash
cd cairo-wadray
python3 -m venv env
source env/bin/activate
```

Install dependencies:

```bash
python -m pip install -r requirements.txt
```

### Run tests

To run the tests:

```bash
pytest
```

## Formal Verification
The WadRay library is not currently formally verified, but it will soon be formally verified by Lindy Labs' formal verification unit. 


## Contribute

We welcome contributions of any kind! Please feel free to submit an issue or open a PR if you have a solution to an existing bug.

## License

This library is released under the [MIT License](LICENSE).
