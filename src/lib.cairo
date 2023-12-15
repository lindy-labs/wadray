mod wadray;
mod wadray_signed;

use wadray::{
    BoundedWad, BoundedRay, DIFF, MAX_CONVERTIBLE_WAD, RAY_ONE, RAY_PERCENT, RAY_SCALE, Ray, RayOneable, RayZeroable, rdiv_wr, rdiv_ww,
    rmul_rw, rmul_wr, WAD_DECIMALS, WAD_ONE, WAD_PERCENT, WAD_SCALE, Wad, WadOneable, WadZeroable, wdiv_rw, wmul_rw,
    wmul_wr,
};
use wadray_signed::{
    BoundedSignedRay, BoundedSignedWad, Signed, SignedRay, SignedRayOneable, SignedRayZeroable, SignedWad,
    SignedWadOneable, SignedWadZeroable,
};
#[cfg(test)]
mod tests {
    mod test_wadray;
    mod test_wadray_signed;
}
