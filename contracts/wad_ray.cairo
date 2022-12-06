from starkware.cairo.common.bool import TRUE
from starkware.cairo.common.math import (
    abs_value,
    assert_le,
    assert_nn_le,
    sign,
    signed_div_rem,
    unsigned_div_rem,
)
from starkware.cairo.common.math_cmp import is_le
from starkware.cairo.common.uint256 import Uint256

from contracts.aliases import ray, ufelt, wad

namespace WadRay {
    const BOUND = 2 ** 125;
    const WAD_SCALE = 10 ** 18;
    const RAY_SCALE = 10 ** 27;
    const WAD_PERCENT = 10 ** 16;
    const RAY_PERCENT = 10 ** 25;
    const DIFF = 10 ** 9;
    const RAY_ONE = RAY_SCALE;
    const WAD_ONE = WAD_SCALE;

    // Reverts if `n` overflows or underflows
    func assert_valid{range_check_ptr}(n) {
        with_attr error_message("WadRay: Out of bounds") {
            assert_le(n, BOUND);
            assert_le(-BOUND, n);
        }
        return ();
    }

    func assert_valid_unsigned{range_check_ptr}(n) {
        with_attr error_message("WadRay: Out of bounds") {
            assert_nn_le(n, BOUND);
        }
        return ();
    }

    func unsigned_min{range_check_ptr}(a, b) -> ufelt {
        assert_valid(a);
        assert_valid(b);

        let le = is_le(a, b);
        if (le == TRUE) {
            return a;
        }
        return b;
    }

    func unsigned_max{range_check_ptr}(a, b) -> ufelt {
        assert_valid_unsigned(a);
        assert_valid_unsigned(b);

        let le = is_le(a, b);
        if (le == TRUE) {
            return b;
        }
        return a;
    }

    func floor{range_check_ptr}(n) -> wad {
        let (int_val, mod_val) = signed_div_rem(n, WAD_ONE, BOUND);
        let floored = n - mod_val;
        assert_valid(floored);
        return floored;
    }

    func ceil{range_check_ptr}(n) -> wad {
        let (int_val, mod_val) = signed_div_rem(n, WAD_ONE, BOUND);

        if (mod_val == 0) {
            tempvar ceiled = n;
            tempvar range_check_ptr = range_check_ptr;
        } else {
            tempvar ceiled = (int_val + 1) * WAD_ONE;
            tempvar range_check_ptr = range_check_ptr;
        }
        assert_valid(ceiled);
        return ceiled;
    }

    func add{range_check_ptr}(a, b) -> wad {
        assert_valid(a);
        assert_valid(b);

        let sum = a + b;
        assert_valid(sum);
        return sum;
    }

    func unsigned_add{range_check_ptr}(a, b) -> wad {
        assert_valid_unsigned(a);
        assert_valid_unsigned(b);

        let sum = a + b;
        assert_valid_unsigned(sum);
        return sum;
    }

    func sub{range_check_ptr}(a, b) -> wad {
        assert_valid(a);
        assert_valid(b);

        let diff = a - b;
        assert_valid(diff);
        return diff;
    }

    func unsigned_sub{range_check_ptr}(a, b) -> wad {
        assert_valid_unsigned(a);
        assert_valid_unsigned(b);

        let diff = a - b;
        assert_valid_unsigned(diff);
        return diff;
    }

    func wmul{range_check_ptr}(a, b) -> wad {
        assert_valid(a);
        assert_valid(b);

        tempvar prod = a * b;
        // `signed_div_rem` asserts -BOUND <= `scaled_prod` < BOUND
        let (scaled_prod, _) = signed_div_rem(prod, WAD_SCALE, BOUND);
        return scaled_prod;
    }

    func wsigned_div{range_check_ptr}(a, b) -> wad {
        alloc_locals;

        assert_valid(a);
        assert_valid(b);

        // `signed_div_rem` assumes 0 < div <= CAIRO_PRIME / rc_bound
        let div = abs_value(b);
        // `sign` assumes -rc_bound < value < rc_bound
        let div_sign = sign(b);
        tempvar prod = a * WAD_SCALE;
        // `signed_div_rem` asserts -BOUND <= `wad_u` < BOUND
        let (wad_u, _) = signed_div_rem(prod, div, BOUND);
        return wad_u * div_sign;
    }

    func wunsigned_div{range_check_ptr}(a, b) -> wad {
        assert_valid_unsigned(a);
        assert_valid_unsigned(b);

        tempvar product = a * WAD_SCALE;
        let (q, _) = unsigned_div_rem(product, b);
        assert_valid(q);
        return q;
    }

    // Assumes both a and b are unsigned
    // No overflow check - use only if the quotient of a and b is guaranteed not to overflow
    func wunsigned_div_unchecked{range_check_ptr}(a, b) -> wad {
        tempvar product = a * WAD_SCALE;
        let (q, _) = unsigned_div_rem(product, b);
        return q;
    }

    // Operations with rays
    func rmul{range_check_ptr}(a, b) -> ray {
        assert_valid(a);
        assert_valid(b);

        tempvar prod = a * b;
        // `signed_div_rem` asserts -BOUND <= `scaled_prod` < BOUND
        let (scaled_prod, _) = signed_div_rem(prod, RAY_SCALE, BOUND);
        return scaled_prod;
    }

    func rsigned_div{range_check_ptr}(a, b) -> ray {
        alloc_locals;

        assert_valid(a);
        assert_valid(b);

        let div = abs_value(b);
        let div_sign = sign(b);
        tempvar prod = a * RAY_SCALE;
        // `signed_div_rem` asserts -BOUND <= `ray_u` < BOUND
        let (ray_u, _) = signed_div_rem(prod, div, BOUND);
        return ray_u * div_sign;
    }

    func runsigned_div{range_check_ptr}(a, b) -> ray {
        assert_valid_unsigned(a);
        assert_valid_unsigned(b);

        tempvar product = a * RAY_SCALE;
        let (q, _) = unsigned_div_rem(product, b);
        assert_valid(q);
        return q;
    }

    // Assumes both a and b are unsigned
    // No overflow check - use only if the quotient of a and b is guaranteed not to overflow
    func runsigned_div_unchecked{range_check_ptr}(a, b) -> ray {
        tempvar product = a * RAY_SCALE;
        let (q, _) = unsigned_div_rem(product, b);
        return q;
    }
    //
    // Conversions
    //

    func to_uint{range_check_ptr}(n) -> (uint: Uint256) {
        assert_valid_unsigned(n);
        let uint = Uint256(low=n, high=0);
        return (uint,);
    }

    func from_uint{range_check_ptr}(n: Uint256) -> wad {
        assert n.high = 0;
        assert_valid_unsigned(n.low);
        return n.low;
    }

    func to_wad{range_check_ptr}(n) -> wad {
        let n_wad = n * WAD_SCALE;
        assert_valid(n_wad);
        return n_wad;
    }

    // Truncates fractional component
    func wad_to_felt{range_check_ptr}(n) -> ufelt {
        let (converted, _) = signed_div_rem(n, WAD_SCALE, BOUND);
        return converted;
    }

    func wad_to_ray{range_check_ptr}(n) -> ray {
        let converted = n * DIFF;
        assert_valid(converted);
        return converted;
    }

    func wad_to_ray_unchecked(n) -> ray {
        return n * DIFF;
    }

    // Truncates a ray to return a wad
    func ray_to_wad{range_check_ptr}(n) -> wad {
        let (converted, _) = unsigned_div_rem(n, DIFF);
        return converted;
    }
}
