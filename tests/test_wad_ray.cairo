%lang starknet

from starkware.cairo.common.uint256 import Uint256

from contracts.aliases import ray, ufelt, wad
from contracts.wad_ray import WadRay

@view
func test_assert_valid{range_check_ptr}(n) {
    WadRay.assert_valid(n);
    return ();
}

@view
func test_assert_valid_unsigned{range_check_ptr}(n) {
    WadRay.assert_valid_unsigned(n);
    return ();
}

@view
func test_floor{range_check_ptr}(n) -> (res: wad) {
    return (WadRay.floor(n),);
}

@view
func test_ceil{range_check_ptr}(n) -> (res: wad) {
    let res: wad = WadRay.ceil(n);
    return (res,);
}

@view
func test_unsigned_max{range_check_ptr}(a, b) -> (res: ufelt) {
    let res: felt = WadRay.unsigned_max(a, b);
    return (res,);
}

@view
func test_unsigned_min{range_check_ptr}(a, b) -> (res: ufelt) {
    let res: felt = WadRay.unsigned_min(a, b);
    return (res,);
}

@view
func test_add{range_check_ptr}(a, b) -> (res: felt) {
    return (WadRay.add(a, b),);
}

@view
func test_unsigned_add{range_check_ptr}(a, b) -> (res: ufelt) {
    return (WadRay.unsigned_add(a, b),);
}

@view
func test_sub{range_check_ptr}(a, b) -> (res: felt) {
    return (WadRay.sub(a, b),);
}

@view
func test_unsigned_sub{range_check_ptr}(a, b) -> (res: ufelt) {
    return (WadRay.unsigned_sub(a, b),);
}

@view
func test_wmul{range_check_ptr}(a, b) -> (res: wad) {
    return (WadRay.wmul(a, b),);
}

@view
func test_wsigned_div{range_check_ptr}(a, b) -> (res: wad) {
    return (WadRay.wsigned_div(a, b),);
}

@view
func test_wunsigned_div{range_check_ptr}(a, b) -> (res: wad) {
    return (WadRay.wunsigned_div(a, b),);
}

@view
func test_wunsigned_div_unchecked{range_check_ptr}(a, b) -> (res: wad) {
    return (WadRay.wunsigned_div_unchecked(a, b),);
}

@view
func test_rmul{range_check_ptr}(a, b) -> (res: ray) {
    return (WadRay.rmul(a, b),);
}

@view
func test_rsigned_div{range_check_ptr}(a, b) -> (res: ray) {
    return (WadRay.rsigned_div(a, b),);
}

@view
func test_runsigned_div{range_check_ptr}(a, b) -> (res: ray) {
    return (WadRay.runsigned_div(a, b),);
}

@view
func test_runsigned_div_unchecked{range_check_ptr}(a, b) -> (res: ray) {
    return (WadRay.runsigned_div_unchecked(a, b),);
}

@view
func test_to_uint{range_check_ptr}(n) -> (uint: Uint256) {
    return WadRay.to_uint(n);
}

@view
func test_from_uint{range_check_ptr}(n: Uint256) -> (res: wad) {
    return (WadRay.from_uint(n),);
}

@view
func test_to_wad{range_check_ptr}(n) -> (res: wad) {
    return (WadRay.to_wad(n),);
}

@view
func test_wad_to_felt{range_check_ptr}(n) -> (res: wad) {
    return (WadRay.wad_to_felt(n),);
}

@view
func test_wad_to_ray{range_check_ptr}(n) -> (res: ray) {
    return (WadRay.wad_to_ray(n),);
}

@view
func test_wad_to_ray_unchecked(n) -> (res: ray) {
    return (WadRay.wad_to_ray_unchecked(n),);
}
