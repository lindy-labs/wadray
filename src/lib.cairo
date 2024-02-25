mod wadray;
mod wadray_signed;

use wadray::{
    BoundedWad, BoundedRay, DIFF, MAX_CONVERTIBLE_WAD, RAY_ONE, RAY_PERCENT, RAY_SCALE, Ray, RayOne, RayZero,
    rdiv_wr, rdiv_ww, rmul_rw, rmul_wr, u128_rdiv, u128_rmul, u128_wdiv, u128_wmul, WAD_DECIMALS, WAD_ONE, WAD_PERCENT,
    WAD_SCALE, Wad, WadOne, WadZero, wdiv_rw, wmul_rw, wmul_wr,
};
use wadray_signed::{
    BoundedSignedRay, BoundedSignedWad, Signed, SignedRay, SignedRayOne, SignedRayZero, SignedWad,
    SignedWadOne, SignedWadZero, wad_to_signed_ray
};
#[cfg(test)]
mod tests {
    mod test_wadray;
    mod test_wadray_signed;
}
