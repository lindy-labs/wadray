use debug::PrintTrait;
use integer::BoundedInt;
use math::Oneable;
use wadray::wadray::{DIFF, Ray, RAY_ONE, rdiv_internal, rmul_internal, Wad, WAD_ONE, wdiv_internal, wmul_internal};

const HALF_PRIME: felt252 = 1809251394333065606848661391547535052811553607665798349986546028067936010240;


#[derive(Copy, Drop, Serde, starknet::Store)]
struct SignedWad {
    val: u128,
    sign: bool
}

#[derive(Copy, Drop, Serde, starknet::Store)]
struct SignedRay {
    val: u128,
    sign: bool
}

//
// Internal helpers
//

fn signed_wad_from_felt(val: felt252) -> SignedWad {
    let wad_val = integer::u128_try_from_felt252(_felt_abs(val)).unwrap();
    SignedWad { val: wad_val, sign: _felt_sign(val) }
}

fn signed_ray_from_felt(val: felt252) -> SignedRay {
    let ray_val = integer::u128_try_from_felt252(_felt_abs(val)).unwrap();
    SignedRay { val: ray_val, sign: _felt_sign(val) }
}

// Returns the sign of a signed `felt252` as with signed magnitude representation
// true = positive
// false = negative
#[inline(always)]
fn _felt_sign(a: felt252) -> bool {
    integer::u256_from_felt252(a) > integer::u256_from_felt252(HALF_PRIME)
}

// Returns the absolute value of a signed `felt252`
fn _felt_abs(a: felt252) -> felt252 {
    let a_sign = _felt_sign(a);

    if !a_sign {
        a
    } else {
        a * -1
    }
}

// Returns the sign of the product in signed multiplication (or quotient in division)
fn sign_from_mul(lhs_sign: bool, rhs_sign: bool) -> bool {
    (!lhs_sign && rhs_sign) || (lhs_sign && !rhs_sign)
}

//
// Trait Implementations
//

// Addition
impl SignedWadAdd of Add<SignedWad> {
    fn add(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        signed_wad_from_felt(lhs.into() + rhs.into())
    }
}

impl SignedWadAddEq of AddEq<SignedWad> {
    #[inline(always)]
    fn add_eq(ref self: SignedWad, other: SignedWad) {
        self = self + other;
    }
}

impl SignedRayAdd of Add<SignedRay> {
    fn add(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        signed_ray_from_felt(lhs.into() + rhs.into())
    }
}

impl SignedRayAddEq of AddEq<SignedRay> {
    #[inline(always)]
    fn add_eq(ref self: SignedRay, other: SignedRay) {
        self = self + other;
    }
}


// Subtraction
impl SignedWadSub of Sub<SignedWad> {
    fn sub(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        signed_wad_from_felt(lhs.into() - rhs.into())
    }
}

impl SignedRaySub of Sub<SignedRay> {
    fn sub(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        signed_ray_from_felt(lhs.into() - rhs.into())
    }
}

impl SignedWadSubEq of SubEq<SignedWad> {
    #[inline(always)]
    fn sub_eq(ref self: SignedWad, other: SignedWad) {
        self = self - other;
    }
}

impl SignedRaySubEq of SubEq<SignedRay> {
    #[inline(always)]
    fn sub_eq(ref self: SignedRay, other: SignedRay) {
        self = self - other;
    }
}


// Multiplication
impl SignedWadMul of Mul<SignedWad> {
    fn mul(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = wmul_internal(lhs.val, rhs.val);
        SignedWad { val: val, sign: sign }
    }
}

impl SignedRayMul of Mul<SignedRay> {
    fn mul(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = rmul_internal(lhs.val, rhs.val);
        SignedRay { val: val, sign: sign }
    }
}

impl SignedWadMulEq of MulEq<SignedWad> {
    #[inline(always)]
    fn mul_eq(ref self: SignedWad, other: SignedWad) {
        self = self * other;
    }
}

impl SignedRayMulEq of MulEq<SignedRay> {
    #[inline(always)]
    fn mul_eq(ref self: SignedRay, other: SignedRay) {
        self = self * other;
    }
}


// Division
impl SignedWadDiv of Div<SignedWad> {
    fn div(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = wdiv_internal(lhs.val, rhs.val);
        SignedWad { val: val, sign: sign }
    }
}

impl SignedRayDiv of Div<SignedRay> {
    fn div(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = rdiv_internal(lhs.val, rhs.val);
        SignedRay { val: val, sign: sign }
    }
}

impl SignedWadDivEq of DivEq<SignedWad> {
    #[inline(always)]
    fn div_eq(ref self: SignedWad, other: SignedWad) {
        self = self / other;
    }
}

impl SignedRayDivEq of DivEq<SignedRay> {
    #[inline(always)]
    fn div_eq(ref self: SignedRay, other: SignedRay) {
        self = self / other;
    }
}


// Conversions
impl U128IntoSignedWad of Into<u128, SignedWad> {
    fn into(self: u128) -> SignedWad {
        SignedWad { val: self, sign: false }
    }
}

impl U128IntoSignedRay of Into<u128, SignedRay> {
    fn into(self: u128) -> SignedRay {
        SignedRay { val: self, sign: false }
    }
}

impl SignedWadIntoFelt252 of Into<SignedWad, felt252> {
    fn into(self: SignedWad) -> felt252 {
        let mag_felt: felt252 = self.val.into();

        if self.sign {
            return mag_felt * -1;
        } else {
            return mag_felt;
        }
    }
}

impl SignedRayIntoFelt252 of Into<SignedRay, felt252> {
    fn into(self: SignedRay) -> felt252 {
        let mag_felt: felt252 = self.val.into();

        if self.sign {
            return mag_felt * -1;
        } else {
            return mag_felt;
        }
    }
}

impl WadIntoSignedWad of Into<Wad, SignedWad> {
    fn into(self: Wad) -> SignedWad {
        SignedWad { val: self.val, sign: false }
    }
}

impl WadIntoSignedRay of Into<Wad, SignedRay> {
    fn into(self: Wad) -> SignedRay {
        SignedRay { val: self.val * DIFF, sign: false }
    }
}

impl RayIntoSignedRay of Into<Ray, SignedRay> {
    fn into(self: Ray) -> SignedRay {
        SignedRay { val: self.val, sign: false }
    }
}

impl SignedWadTryIntoWad of TryInto<SignedWad, Wad> {
    fn try_into(self: SignedWad) -> Option<Wad> {
        if !self.sign {
            return Option::Some(Wad { val: self.val });
        } else {
            return Option::None;
        }
    }
}

impl SignedRayTryIntoRay of TryInto<SignedRay, Ray> {
    fn try_into(self: SignedRay) -> Option<Ray> {
        if !self.sign {
            return Option::Some(Ray { val: self.val });
        } else {
            return Option::None;
        }
    }
}


// Comparisons
impl SignedWadPartialEq of PartialEq<SignedWad> {
    fn eq(lhs: @SignedWad, rhs: @SignedWad) -> bool {
        let val_cmp: bool = *lhs.val == *rhs.val;
        if val_cmp && (*lhs.val).is_zero() {
            true
        } else {
            val_cmp && *lhs.sign == *rhs.sign
        }
    }

    fn ne(lhs: @SignedWad, rhs: @SignedWad) -> bool {
        !(*lhs == *rhs)
    }
}

impl SignedWadPartialOrd of PartialOrd<SignedWad> {
    #[inline(always)]
    fn le(lhs: SignedWad, rhs: SignedWad) -> bool {
        !(lhs > rhs)
    }

    #[inline(always)]
    fn ge(lhs: SignedWad, rhs: SignedWad) -> bool {
        !(lhs < rhs)
    }

    #[inline(always)]
    fn lt(lhs: SignedWad, rhs: SignedWad) -> bool {
        if lhs.sign != rhs.sign {
            if lhs.val == rhs.val && lhs.is_zero() {
                false
            } else {
                lhs.sign
            }
        } else {
            (lhs.val != rhs.val) && ((lhs.val < rhs.val) ^ lhs.sign)
        }
    }

    #[inline(always)]
    fn gt(lhs: SignedWad, rhs: SignedWad) -> bool {
        if lhs.sign != rhs.sign {
            if lhs.val == rhs.val && lhs.is_zero() {
                false
            } else {
                !lhs.sign
            }
        } else {
            (lhs.val != rhs.val) && ((lhs.val > rhs.val) ^ lhs.sign)
        }
    }
}

impl SignedRayPartialEq of PartialEq<SignedRay> {
    fn eq(lhs: @SignedRay, rhs: @SignedRay) -> bool {
        let val_cmp: bool = *lhs.val == *rhs.val;
        if val_cmp && (*lhs.val).is_zero() {
            true
        } else {
            val_cmp && *lhs.sign == *rhs.sign
        }
    }

    fn ne(lhs: @SignedRay, rhs: @SignedRay) -> bool {
        !(*lhs == *rhs)
    }
}

impl SignedRayPartialOrd of PartialOrd<SignedRay> {
    #[inline(always)]
    fn le(lhs: SignedRay, rhs: SignedRay) -> bool {
        !(lhs > rhs)
    }

    #[inline(always)]
    fn ge(lhs: SignedRay, rhs: SignedRay) -> bool {
        !(lhs < rhs)
    }

    #[inline(always)]
    fn lt(lhs: SignedRay, rhs: SignedRay) -> bool {
        if lhs.sign != rhs.sign {
            if lhs.val == rhs.val && lhs.is_zero() {
                false
            } else {
                lhs.sign
            }
        } else {
            (lhs.val != rhs.val) && ((lhs.val < rhs.val) ^ lhs.sign)
        }
    }

    #[inline(always)]
    fn gt(lhs: SignedRay, rhs: SignedRay) -> bool {
        if lhs.sign != rhs.sign {
            if lhs.val == rhs.val && lhs.is_zero() {
                false
            } else {
                !lhs.sign
            }
        } else {
            (lhs.val != rhs.val) && ((lhs.val > rhs.val) ^ lhs.sign)
        }
    }
}


// Bounded
impl BoundedSignedWad of BoundedInt<SignedWad> {
    #[inline(always)]
    fn min() -> SignedWad nopanic {
        SignedWad { val: integer::BoundedU128::max(), sign: true }
    }

    #[inline(always)]
    fn max() -> SignedWad nopanic {
        SignedWad { val: integer::BoundedU128::max(), sign: false }
    }
}

impl BoundedSignedRay of BoundedInt<SignedRay> {
    #[inline(always)]
    fn min() -> SignedRay nopanic {
        SignedRay { val: integer::BoundedU128::max(), sign: true }
    }

    #[inline(always)]
    fn max() -> SignedRay nopanic {
        SignedRay { val: integer::BoundedU128::max(), sign: false }
    }
}


// Zeroable
impl SignedWadZeroable of Zeroable<SignedWad> {
    #[inline(always)]
    fn zero() -> SignedWad {
        SignedWad { val: 0, sign: false }
    }

    #[inline(always)]
    fn is_zero(self: SignedWad) -> bool {
        self.val == 0
    }

    #[inline(always)]
    fn is_non_zero(self: SignedWad) -> bool {
        self.val != 0
    }
}

impl SignedRayZeroable of Zeroable<SignedRay> {
    #[inline(always)]
    fn zero() -> SignedRay {
        SignedRay { val: 0, sign: false }
    }

    #[inline(always)]
    fn is_zero(self: SignedRay) -> bool {
        self.val == 0
    }

    #[inline(always)]
    fn is_non_zero(self: SignedRay) -> bool {
        self.val != 0
    }
}


// Oneable
impl SignedWadOneable of Oneable<SignedWad> {
    #[inline(always)]
    fn one() -> SignedWad {
        SignedWad { val: WAD_ONE, sign: false }
    }

    #[inline(always)]
    fn is_one(self: SignedWad) -> bool {
        self.val == WAD_ONE && !self.sign
    }

    #[inline(always)]
    fn is_non_one(self: SignedWad) -> bool {
        self.val != WAD_ONE || self.sign
    }
}

impl SignedRayOneable of Oneable<SignedRay> {
    #[inline(always)]
    fn one() -> SignedRay {
        SignedRay { val: RAY_ONE, sign: false }
    }

    #[inline(always)]
    fn is_one(self: SignedRay) -> bool {
        self.val == RAY_ONE && !self.sign
    }

    #[inline(always)]
    fn is_non_one(self: SignedRay) -> bool {
        self.val != RAY_ONE || self.sign
    }
}


// Signed
trait Signed<T> {
    fn is_negative(self: T) -> bool;
    fn is_positive(self: T) -> bool;
}

impl SignedWadSigned of Signed<SignedWad> {
    fn is_negative(self: SignedWad) -> bool {
        self.val > 0 && self.sign
    }

    fn is_positive(self: SignedWad) -> bool {
        self.val > 0 && !self.sign
    }
}

impl SignedRaySigned of Signed<SignedRay> {
    fn is_negative(self: SignedRay) -> bool {
        self.val > 0 && self.sign
    }

    fn is_positive(self: SignedRay) -> bool {
        self.val > 0 && !self.sign
    }
}
