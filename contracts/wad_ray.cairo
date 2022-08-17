from starkware.cairo.common.math import (
    assert_le,
    assert_nn_le,
    sign,
    abs_value,
    signed_div_rem,
    unsigned_div_rem,
)

from starkware.cairo.common.uint256 import Uint256

namespace WadRay:
    const BOUND = 2 ** 125
    const WAD_SCALE = 10 ** 18
    const RAY_SCALE = 10 ** 27
    const WAD_PERCENT = 10 ** 16
    const RAY_PERCENT = 10 ** 25
    const DIFF = 10 ** 9
    const RAY_ONE = RAY_SCALE
    const WAD_ONE = WAD_SCALE

    func assert_result_valid{range_check_ptr}(n):
        with_attr error_message("WadRay: Result is out of bounds"):
            assert_le(n, BOUND)
            assert_le(-BOUND, n)
        end
        return ()
    end

    func assert_result_valid_unsigned{range_check_ptr}(n):
        with_attr error_message("WadRay: Result is out of bounds"):
            assert_nn_le(n, BOUND)
        end
        return ()
    end

    func floor{range_check_ptr}(n) -> (wad):
        let (int_val, mod_val) = signed_div_rem(n, WAD_ONE, BOUND)
        let floored = n - mod_val
        assert_result_valid(floored)
        return (wad=floored)
    end

    func ceil{range_check_ptr}(n) -> (wad):
        let (int_val, mod_val) = signed_div_rem(n, WAD_ONE, BOUND)

        if mod_val == 0:
            tempvar ceiled = n
            tempvar range_check_ptr = range_check_ptr
        else:
            tempvar ceiled = (int_val + 1) * WAD_ONE
            tempvar range_check_ptr = range_check_ptr
        end
        assert_result_valid(ceiled)
        return (wad=ceiled)
    end

    func add{range_check_ptr}(a, b) -> (wad):
        let sum = a + b
        assert_result_valid(sum)
        return (wad=sum)
    end

    func add_unsigned{range_check_ptr}(a, b) -> (wad):
        let sum = a + b
        assert_result_valid_unsigned(sum)
        return (wad=sum)
    end

    func sub{range_check_ptr}(a, b) -> (wad):
        let diff = a - b
        assert_result_valid(diff)
        return (wad=diff)
    end

    func sub_unsigned{range_check_ptr}(a, b) -> (wad):
        let diff = a - b
        assert_result_valid_unsigned(diff)
        return (wad=diff)
    end

    func wmul{range_check_ptr}(a, b) -> (wad):
        tempvar prod = a * b
        # `signed_div_rem` asserts -BOUND <= `scaled_prod` < BOUND
        let (scaled_prod, _) = signed_div_rem(prod, WAD_SCALE, BOUND)
        return (wad=scaled_prod)
    end

    func wsigned_div{range_check_ptr}(a, b) -> (wad):
        alloc_locals
        # `signed_div_rem` assumes 0 < div <= PRIME / rc_bound
        let (div) = abs_value(b)
        # `sign` assumes -rc_bound < value < rc_bound
        let (div_sign) = sign(b)
        tempvar prod = a * WAD_SCALE
        # `signed_div_rem` asserts -BOUND <= `wad_u` < BOUND
        let (wad_u, _) = signed_div_rem(prod, div, BOUND)
        return (wad=wad_u * div_sign)
    end

    func wunsigned_div{range_check_ptr}(a, b) -> (wad):
        tempvar product = a * WAD_SCALE
        let (q, _) = unsigned_div_rem(product, b)
        assert_result_valid(q)
        return (wad=q)
    end

    # No overflow check - use only if the quotient of `a` and `b` is guaranteed not to overflow
    func wunsigned_div_unchecked{range_check_ptr}(a, b) -> (wad):
        tempvar product = a * WAD_SCALE
        let (q, _) = unsigned_div_rem(product, b)
        return (wad=q)
    end

    func rmul{range_check_ptr}(a, b) -> (ray):
        tempvar prod = a * b
        # `signed_div_rem` asserts -BOUND <= `scaled_prod` < BOUND
        let (scaled_prod, _) = signed_div_rem(prod, RAY_SCALE, BOUND)
        return (ray=scaled_prod)
    end

    func rsigned_div{range_check_ptr}(a, b) -> (ray):
        alloc_locals
        let (div) = abs_value(b)
        let (div_sign) = sign(b)
        tempvar prod = a * RAY_SCALE
        # `signed_div_rem` asserts -BOUND <= `ray_u` < BOUND
        let (ray_u, _) = signed_div_rem(prod, div, BOUND)
        return (ray=ray_u * div_sign)
    end

    func runsigned_div{range_check_ptr}(a, b) -> (ray):
        tempvar product = a * RAY_SCALE
        let (q, _) = unsigned_div_rem(product, b)
        assert_result_valid(q)
        return (ray=q)
    end

    # No overflow check - use only if the quotient of `a` and `b` is guaranteed not to overflow
    func runsigned_div_unchecked{range_check_ptr}(a, b) -> (ray):
        tempvar product = a * RAY_SCALE
        let (q, _) = unsigned_div_rem(product, b)
        return (ray=q)
    end

    #
    # Conversions
    #

    func to_uint(n) -> (uint : Uint256):
        let uint = Uint256(low=n, high=0)
        return (uint)
    end

    func from_uint{range_check_ptr}(n : Uint256) -> (wad):
        assert n.high = 0
        assert_result_valid(n.low)
        return (wad=n.low)
    end

    func to_wad{range_check_ptr}(n) -> (wad):
        let n_wad = n * WAD_SCALE
        assert_result_valid(n_wad)
        return (wad=n_wad)
    end

    # Truncates fractional component
    func wad_to_felt{range_check_ptr}(n) -> (wad):
        let (wad, _) = signed_div_rem(n, WAD_SCALE, BOUND)
        return (wad)
    end

    func wad_to_ray{range_check_ptr}(n) -> (ray):
        let ray = n * DIFF
        assert_result_valid(ray)
        return (ray)
    end

    func wad_to_ray_unchecked(n) -> (ray):
        return (ray=n * DIFF)
    end

    # Truncates a ray to return a wad
    func ray_to_wad{range_check_ptr}(n) -> (wad):
        let (wad, _) = unsigned_div_rem(n, DIFF)
        return (wad)
    end
end
