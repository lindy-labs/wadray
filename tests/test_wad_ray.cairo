%lang starknet

from starkware.cairo.common.uint256 import Uint256

from contracts.wad_ray import WadRay

@view
func test_assert_result_valid{range_check_ptr}(n):
    WadRay.assert_result_valid(n)
    return ()
end

@view
func test_assert_result_valid_unsigned{range_check_ptr}(n):
    WadRay.assert_result_valid_unsigned(n)
    return ()
end

@view
func test_floor{range_check_ptr}(n) -> (wad):
    return WadRay.floor(n)
end

@view
func test_ceil{range_check_ptr}(n) -> (wad):
    return WadRay.ceil(n)
end

@view
func test_add{range_check_ptr}(a, b) -> (wad):
    return WadRay.add(a, b)
end

@view
func test_add_unsigned{range_check_ptr}(a, b) -> (wad):
    return WadRay.add_unsigned(a, b)
end

@view
func test_sub{range_check_ptr}(a, b) -> (wad):
    return WadRay.sub(a, b)
end

@view
func test_sub_unsigned{range_check_ptr}(a, b) -> (wad):
    return WadRay.sub_unsigned(a, b)
end

@view
func test_wmul{range_check_ptr}(a, b) -> (wad):
    return WadRay.wmul(a, b)
end

@view
func test_wsigned_div{range_check_ptr}(a, b) -> (wad):
    return WadRay.wsigned_div(a, b)
end

@view
func test_wunsigned_div{range_check_ptr}(a, b) -> (wad):
    return WadRay.wunsigned_div(a, b)
end

@view
func test_wunsigned_div_unchecked{range_check_ptr}(a, b) -> (wad):
    return WadRay.wunsigned_div_unchecked(a, b)
end

@view
func test_rmul{range_check_ptr}(a, b) -> (ray):
    return WadRay.rmul(a, b)
end

@view
func test_rsigned_div{range_check_ptr}(a, b) -> (ray):
    return WadRay.rsigned_div(a, b)
end

@view
func test_runsigned_div{range_check_ptr}(a, b) -> (ray):
    return WadRay.runsigned_div(a, b)
end

@view
func test_runsigned_div_unchecked{range_check_ptr}(a, b) -> (ray):
    return WadRay.runsigned_div_unchecked(a, b)
end

@view
func test_to_uint(n) -> (uint : Uint256):
    return WadRay.to_uint(n)
end

@view
func test_from_uint{range_check_ptr}(n : Uint256) -> (wad):
    return WadRay.from_uint(n)
end

@view
func test_to_wad{range_check_ptr}(n) -> (wad):
    return WadRay.to_wad(n)
end

@view
func test_wad_to_felt{range_check_ptr}(n) -> (wad):
    return WadRay.wad_to_felt(n)
end

@view
func test_wad_to_ray{range_check_ptr}(n) -> (ray):
    return WadRay.wad_to_ray(n)
end

@view
func test_wad_to_ray_unchecked(n) -> (ray):
    return WadRay.wad_to_ray_unchecked(n)
end
