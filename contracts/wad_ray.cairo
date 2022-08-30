from starkware.cairo.common.math import (
    assert_le,
    assert_nn_le,
    sign,
    abs_value,
    signed_div_rem,
    unsigned_div_rem,
)

from starkware.cairo.common.uint256 import Uint256

namespace WadRay {
    const BOUND = 2 ** 125;
    const WAD_SCALE = 10 ** 18;
    const RAY_SCALE = 10 ** 27;
    const WAD_PERCENT = 10 ** 16;
    const RAY_PERCENT = 10 ** 25;
    const DIFF = 10 ** 9;
    const RAY_ONE = RAY_SCALE;
    const WAD_ONE = WAD_SCALE;

    func assert_result_valid{range_check_ptr}(n) {
        with_attr error_message("WadRay: Result is out of bounds") {
            assert_le(n, BOUND);
            assert_le(-BOUND, n);
        }
        return ();
    }

    func assert_result_valid_unsigned{range_check_ptr}(n) {
        with_attr error_message("WadRay: Result is out of bounds") {
            assert_nn_le(n, BOUND);
        }
        return ();
    }

    func floor{range_check_ptr}(n) -> (wad: felt) {
        let (int_val, mod_val) = signed_div_rem(n, WAD_ONE, BOUND);
        let floored = n - mod_val;
        assert_result_valid(floored);
        return (wad=floored);
    }

    func ceil{range_check_ptr}(n) -> (wad: felt) {
        let (int_val, mod_val) = signed_div_rem(n, WAD_ONE, BOUND);

        if (mod_val == 0) {
            tempvar ceiled = n;
            tempvar range_check_ptr = range_check_ptr;
        } else {
            tempvar ceiled = (int_val + 1) * WAD_ONE;
            tempvar range_check_ptr = range_check_ptr;
        }
        assert_result_valid(ceiled);
        return (wad=ceiled);
    }

    func add{range_check_ptr}(a, b) -> (wad: felt) {
        let sum = a + b;
        assert_result_valid(sum);
        return (wad=sum);
    }

    func add_unsigned{range_check_ptr}(a, b) -> (wad: felt) {
        let sum = a + b;
        assert_result_valid_unsigned(sum);
        return (wad=sum);
    }

    func sub{range_check_ptr}(a, b) -> (wad: felt) {
        let diff = a - b;
        assert_result_valid(diff);
        return (wad=diff);
    }

    func sub_unsigned{range_check_ptr}(a, b) -> (wad: felt) {
        let diff = a - b;
        assert_result_valid_unsigned(diff);
        return (wad=diff);
    }

    func wmul{range_check_ptr}(a, b) -> (wad: felt) {
        tempvar prod = a * b;
        // `signed_div_rem` asserts -BOUND <= `scaled_prod` < BOUND
        let (scaled_prod, _) = signed_div_rem(prod, WAD_SCALE, BOUND);
        return (wad=scaled_prod);
    }

    func wsigned_div{range_check_ptr}(a, b) -> (wad: felt) {
        alloc_locals;
        // `signed_div_rem` assumes 0 < div <= PRIME / rc_bound
        let div = abs_value(b);
        // `sign` assumes -rc_bound < value < rc_bound
        let div_sign = sign(b);
        tempvar prod = a * WAD_SCALE;
        // `signed_div_rem` asserts -BOUND <= `wad_u` < BOUND
        let (wad_u, _) = signed_div_rem(prod, div, BOUND);
        return (wad=wad_u * div_sign);
    }

    func wunsigned_div{range_check_ptr}(a, b) -> (wad: felt) {
        tempvar product = a * WAD_SCALE;
        let (q, _) = unsigned_div_rem(product, b);
        assert_result_valid(q);
        return (wad=q);
    }

    // No overflow check - use only if the quotient of `a` and `b` is guaranteed not to overflow
    func wunsigned_div_unchecked{range_check_ptr}(a, b) -> (wad: felt) {
        tempvar product = a * WAD_SCALE;
        let (q, _) = unsigned_div_rem(product, b);
        return (wad=q);
    }

    func rmul{range_check_ptr}(a, b) -> (ray: felt) {
        tempvar prod = a * b;
        // `signed_div_rem` asserts -BOUND <= `scaled_prod` < BOUND
        let (scaled_prod, _) = signed_div_rem(prod, RAY_SCALE, BOUND);
        return (ray=scaled_prod);
    }

    func rsigned_div{range_check_ptr}(a, b) -> (ray: felt) {
        alloc_locals;
        let div = abs_value(b);
        let div_sign = sign(b);
        tempvar prod = a * RAY_SCALE;
        // `signed_div_rem` asserts -BOUND <= `ray_u` < BOUND
        let (ray_u, _) = signed_div_rem(prod, div, BOUND);
        return (ray=ray_u * div_sign);
    }

    func runsigned_div{range_check_ptr}(a, b) -> (ray: felt) {
        tempvar product = a * RAY_SCALE;
        let (q, _) = unsigned_div_rem(product, b);
        assert_result_valid(q);
        return (ray=q);
    }

    // No overflow check - use only if the quotient of `a` and `b` is guaranteed not to overflow
    func runsigned_div_unchecked{range_check_ptr}(a, b) -> (ray: felt) {
        tempvar product = a * RAY_SCALE;
        let (q, _) = unsigned_div_rem(product, b);
        return (ray=q);
    }

    //
    // Conversions
    //

    func to_uint(n) -> (uint: Uint256) {
        let uint = Uint256(low=n, high=0);
        return (uint,);
    }

    func from_uint{range_check_ptr}(n: Uint256) -> (wad: felt) {
        assert n.high = 0;
        assert_result_valid(n.low);
        return (wad=n.low);
    }

    func to_wad{range_check_ptr}(n) -> (wad: felt) {
        let n_wad = n * WAD_SCALE;
        assert_result_valid(n_wad);
        return (wad=n_wad);
    }

    // Truncates fractional component
    func wad_to_felt{range_check_ptr}(n) -> (wad: felt) {
        let (wad, _) = signed_div_rem(n, WAD_SCALE, BOUND);
        return (wad,);
    }

    func wad_to_ray{range_check_ptr}(n) -> (ray: felt) {
        let ray = n * DIFF;
        assert_result_valid(ray);
        return (ray,);
    }

    func wad_to_ray_unchecked(n) -> (ray: felt) {
        return (ray=n * DIFF);
    }

    // Truncates a ray to return a wad
    func ray_to_wad{range_check_ptr}(n) -> (wad: felt) {
        let (wad, _) = unsigned_div_rem(n, DIFF);
        return (wad,);
    }
}
