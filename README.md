# WadRay library for Cairo

This library provides a felt-based implementation of arithmetic functions for two types of fixed-point decimal numbers, `wad` (18 decimals of precision) and `ray` (27 decimals of decimal numbers), written in Cairo for [StarkNet](https://www.cairo-lang.org/docs/).

The design of this library was originally inspired by Influenceth's [64x61 fixed-point math library](https://github.com/influenceth/cairo-math-64x61).


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
) -> (c: felt):
    let c: felt = WadRay.add(a, b)
    return (c)
end
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

## Contribute

We welcome contributions of any kind! Please feel free to submit an issue or open a PR if you have a solution to an existing bug.

## License

This library is released under the [MIT License](LICENSE).
