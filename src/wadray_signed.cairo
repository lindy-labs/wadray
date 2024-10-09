use core::fmt::{Debug, Display, Error, Formatter};
use core::num::traits::{One, Zero, Bounded};
use core::ops::{AddAssign, SubAssign, MulAssign, DivAssign};
use core::traits::{Default, Neg};
use starknet::storage_access::StorePacking;
use wadray::wadray::{DIFF, Ray, RAY_ONE, u128_rdiv, u128_rmul, u128_wdiv, u128_wmul, Wad, WAD_ONE};

const HALF_PRIME: u256 = 1809251394333065606848661391547535052811553607665798349986546028067936010240;

#[derive(Copy, Drop, Serde)]
pub struct SignedWad {
    pub val: u128,
    pub sign: bool
}

#[derive(Copy, Drop, Serde)]
pub struct SignedRay {
    pub val: u128,
    pub sign: bool
}

// External helpers
pub fn wad_to_signed_ray(a: Wad) -> SignedRay {
    SignedRay { val: a.val * DIFF, sign: false }
}

//
// Internal helpers
//

fn signed_wad_from_felt(val: felt252) -> SignedWad {
    let wad_val = felt_abs(val).try_into().unwrap();
    SignedWad { val: wad_val, sign: felt_sign(val) }
}

fn signed_ray_from_felt(val: felt252) -> SignedRay {
    let ray_val = felt_abs(val).try_into().unwrap();
    SignedRay { val: ray_val, sign: felt_sign(val) }
}

// Returns the sign of a signed `felt252` as with signed magnitude representation
// true = positive
// false = negative
#[inline]
fn felt_sign(a: felt252) -> bool {
    a.into() > HALF_PRIME
}

// Returns the absolute value of a signed `felt252`
fn felt_abs(a: felt252) -> felt252 {
    let a_sign = felt_sign(a);

    if !a_sign {
        a
    } else {
        a * -1
    }
}

// Returns the sign of the product in signed multiplication (or quotient in division)
fn sign_from_mul(lhs_sign: bool, rhs_sign: bool) -> bool {
    lhs_sign ^ rhs_sign
}

fn pack(val: u128, sign: bool) -> felt252 {
    // shift by 2**128
    let two_pow_128: felt252 = 340282366920938463463374607431768211456;
    val.into() + sign.into() * two_pow_128
}

fn unpack(packed: felt252) -> (u128, bool) {
    let shift: NonZero<u256> = 340282366920938463463374607431768211456; // 2**128
    let (sign, val) = DivRem::<u256>::div_rem(packed.into(), shift);
    let val: u128 = val.try_into().expect('WadRay Signed val unpacking');
    let sign: u128 = sign.try_into().expect('WadRay Signed sign unpacking');
    (val, sign == 1)
}

//
// Trait Implementations
//

// StorePacking
pub impl SignedWadStorePacking of StorePacking<SignedWad, felt252> {
    fn pack(value: SignedWad) -> felt252 {
        pack(value.val, value.sign)
    }

    fn unpack(value: felt252) -> SignedWad {
        let (val, sign) = unpack(value);
        SignedWad { val, sign }
    }
}

pub impl SignedRayStorePacking of StorePacking<SignedRay, felt252> {
    fn pack(value: SignedRay) -> felt252 {
        pack(value.val, value.sign)
    }

    fn unpack(value: felt252) -> SignedRay {
        let (val, sign) = unpack(value);
        SignedRay { val, sign }
    }
}

// Addition
pub impl SignedWadAdd of Add<SignedWad> {
    fn add(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        signed_wad_from_felt(lhs.into() + rhs.into())
    }
}

pub impl SignedWadAddAsign of AddAssign<SignedWad, SignedWad> {
    #[inline]
    fn add_assign(ref self: SignedWad, rhs: SignedWad) {
        self = self + rhs;
    }
}

pub impl SignedRayAdd of Add<SignedRay> {
    fn add(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        signed_ray_from_felt(lhs.into() + rhs.into())
    }
}

pub impl SignedRayAddAssign of AddAssign<SignedRay, SignedRay> {
    #[inline]
    fn add_assign(ref self: SignedRay, rhs: SignedRay) {
        self = self + rhs;
    }
}


// Subtraction
pub impl SignedWadSub of Sub<SignedWad> {
    fn sub(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        signed_wad_from_felt(lhs.into() - rhs.into())
    }
}

pub impl SignedRaySub of Sub<SignedRay> {
    fn sub(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        signed_ray_from_felt(lhs.into() - rhs.into())
    }
}

pub impl SignedWadSubAssign of SubAssign<SignedWad, SignedWad> {
    #[inline]
    fn sub_assign(ref self: SignedWad, rhs: SignedWad) {
        self = self - rhs;
    }
}

pub impl SignedRaySubAssign of SubAssign<SignedRay, SignedRay> {
    #[inline]
    fn sub_assign(ref self: SignedRay, rhs: SignedRay) {
        self = self - rhs;
    }
}


// Multiplication
pub impl SignedWadMul of Mul<SignedWad> {
    fn mul(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = u128_wmul(lhs.val, rhs.val);
        SignedWad { val: val, sign: sign }
    }
}

pub impl SignedRayMul of Mul<SignedRay> {
    fn mul(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = u128_rmul(lhs.val, rhs.val);
        SignedRay { val: val, sign: sign }
    }
}

pub impl SignedWadMulAssign of MulAssign<SignedWad, SignedWad> {
    #[inline]
    fn mul_assign(ref self: SignedWad, rhs: SignedWad) {
        self = self * rhs;
    }
}

pub impl SignedRayMulAssign of MulAssign<SignedRay, SignedRay> {
    #[inline]
    fn mul_assign(ref self: SignedRay, rhs: SignedRay) {
        self = self * rhs;
    }
}


// Division
pub impl SignedWadDiv of Div<SignedWad> {
    fn div(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = u128_wdiv(lhs.val, rhs.val);
        SignedWad { val: val, sign: sign }
    }
}

pub impl SignedRayDiv of Div<SignedRay> {
    fn div(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = u128_rdiv(lhs.val, rhs.val);
        SignedRay { val: val, sign: sign }
    }
}

pub impl SignedWadDivAssign of DivAssign<SignedWad, SignedWad> {
    #[inline]
    fn div_assign(ref self: SignedWad, rhs: SignedWad) {
        self = self / rhs;
    }
}

pub impl SignedRayDivAssign of DivAssign<SignedRay, SignedRay> {
    #[inline]
    fn div_assign(ref self: SignedRay, rhs: SignedRay) {
        self = self / rhs;
    }
}


// Conversions
pub impl U128IntoSignedWad of Into<u128, SignedWad> {
    fn into(self: u128) -> SignedWad {
        SignedWad { val: self, sign: false }
    }
}

pub impl U128IntoSignedRay of Into<u128, SignedRay> {
    fn into(self: u128) -> SignedRay {
        SignedRay { val: self, sign: false }
    }
}

pub impl SignedWadIntoFelt252 of Into<SignedWad, felt252> {
    fn into(self: SignedWad) -> felt252 {
        let mag_felt: felt252 = self.val.into();

        if self.sign {
            return mag_felt * -1;
        } else {
            return mag_felt;
        }
    }
}

pub impl SignedRayIntoFelt252 of Into<SignedRay, felt252> {
    fn into(self: SignedRay) -> felt252 {
        let mag_felt: felt252 = self.val.into();

        if self.sign {
            return mag_felt * -1;
        } else {
            return mag_felt;
        }
    }
}

pub impl WadIntoSignedWad of Into<Wad, SignedWad> {
    fn into(self: Wad) -> SignedWad {
        SignedWad { val: self.val, sign: false }
    }
}

pub impl RayIntoSignedRay of Into<Ray, SignedRay> {
    fn into(self: Ray) -> SignedRay {
        SignedRay { val: self.val, sign: false }
    }
}

pub impl SignedWadTryIntoWad of TryInto<SignedWad, Wad> {
    fn try_into(self: SignedWad) -> Option<Wad> {
        if !self.sign || self.is_zero() {
            return Option::Some(Wad { val: self.val });
        } else {
            return Option::None;
        }
    }
}

pub impl SignedRayTryIntoRay of TryInto<SignedRay, Ray> {
    fn try_into(self: SignedRay) -> Option<Ray> {
        if !self.sign || self.is_zero() {
            return Option::Some(Ray { val: self.val });
        } else {
            return Option::None;
        }
    }
}


// Comparisons
pub impl SignedWadPartialEq of PartialEq<SignedWad> {
    fn eq(lhs: @SignedWad, rhs: @SignedWad) -> bool {
        let val_cmp: bool = *lhs.val == *rhs.val;
        if val_cmp && lhs.is_zero() {
            true
        } else {
            val_cmp && *lhs.sign == *rhs.sign
        }
    }

    fn ne(lhs: @SignedWad, rhs: @SignedWad) -> bool {
        !(*lhs == *rhs)
    }
}

pub impl SignedWadPartialOrd of PartialOrd<SignedWad> {
    #[inline]
    fn le(lhs: SignedWad, rhs: SignedWad) -> bool {
        !(lhs > rhs)
    }

    #[inline]
    fn ge(lhs: SignedWad, rhs: SignedWad) -> bool {
        !(lhs < rhs)
    }

    #[inline]
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

    #[inline]
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

pub impl SignedRayPartialEq of PartialEq<SignedRay> {
    fn eq(lhs: @SignedRay, rhs: @SignedRay) -> bool {
        let val_cmp: bool = *lhs.val == *rhs.val;
        if val_cmp && lhs.is_zero() {
            true
        } else {
            val_cmp && *lhs.sign == *rhs.sign
        }
    }

    fn ne(lhs: @SignedRay, rhs: @SignedRay) -> bool {
        !(*lhs == *rhs)
    }
}

pub impl SignedRayPartialOrd of PartialOrd<SignedRay> {
    #[inline]
    fn le(lhs: SignedRay, rhs: SignedRay) -> bool {
        !(lhs > rhs)
    }

    #[inline]
    fn ge(lhs: SignedRay, rhs: SignedRay) -> bool {
        !(lhs < rhs)
    }

    #[inline]
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

    #[inline]
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
pub impl BoundedSignedWad of Bounded<SignedWad> {
    const MAX: SignedWad = SignedWad { val: Bounded::MAX, sign: false };

    const MIN: SignedWad = SignedWad { val: Bounded::MAX, sign: true };
}

pub impl BoundedSignedRay of Bounded<SignedRay> {
    const MAX: SignedRay = SignedRay { val: Bounded::MAX, sign: false };

    const MIN: SignedRay = SignedRay { val: Bounded::MAX, sign: true };
}


// Zero
pub impl SignedWadZero of Zero<SignedWad> {
    #[inline]
    fn zero() -> SignedWad {
        SignedWad { val: 0, sign: false }
    }

    #[inline]
    fn is_zero(self: @SignedWad) -> bool {
        *self.val == 0
    }

    #[inline]
    fn is_non_zero(self: @SignedWad) -> bool {
        *self.val != 0
    }
}

pub impl SignedRayZero of Zero<SignedRay> {
    #[inline]
    fn zero() -> SignedRay {
        SignedRay { val: 0, sign: false }
    }

    #[inline]
    fn is_zero(self: @SignedRay) -> bool {
        *self.val == 0
    }

    #[inline]
    fn is_non_zero(self: @SignedRay) -> bool {
        *self.val != 0
    }
}


// One
pub impl SignedWadOne of One<SignedWad> {
    #[inline]
    fn one() -> SignedWad {
        SignedWad { val: WAD_ONE, sign: false }
    }

    #[inline]
    fn is_one(self: @SignedWad) -> bool {
        *self.val == WAD_ONE && !*self.sign
    }

    #[inline]
    fn is_non_one(self: @SignedWad) -> bool {
        *self.val != WAD_ONE || *self.sign
    }
}

pub impl SignedRayOne of One<SignedRay> {
    #[inline]
    fn one() -> SignedRay {
        SignedRay { val: RAY_ONE, sign: false }
    }

    #[inline]
    fn is_one(self: @SignedRay) -> bool {
        *self.val == RAY_ONE && !*self.sign
    }

    #[inline]
    fn is_non_one(self: @SignedRay) -> bool {
        *self.val != RAY_ONE || *self.sign
    }
}


// Signed
pub trait Signed<T> {
    fn is_negative(self: T) -> bool;
    fn is_positive(self: T) -> bool;
}

pub impl SignedWadSigned of Signed<SignedWad> {
    fn is_negative(self: SignedWad) -> bool {
        self.val > 0 && self.sign
    }

    fn is_positive(self: SignedWad) -> bool {
        self.val > 0 && !self.sign
    }
}

pub impl SignedRaySigned of Signed<SignedRay> {
    fn is_negative(self: SignedRay) -> bool {
        self.val > 0 && self.sign
    }

    fn is_positive(self: SignedRay) -> bool {
        self.val > 0 && !self.sign
    }
}


// Display and Debug
pub impl DisplaySignedWad of Display<SignedWad> {
    fn fmt(self: @SignedWad, ref f: Formatter) -> Result<(), Error> {
        if *self.sign {
            write!(f, "-")?;
        }

        Display::fmt(self.val, ref f)
    }
}

pub impl DisplaySignedRay of Display<SignedRay> {
    fn fmt(self: @SignedRay, ref f: Formatter) -> Result<(), Error> {
        if *self.sign {
            write!(f, "-")?;
        }

        Display::fmt(self.val, ref f)
    }
}

pub impl DebugSignedWad of Debug<SignedWad> {
    fn fmt(self: @SignedWad, ref f: Formatter) -> Result<(), Error> {
        Display::fmt(self, ref f)
    }
}

pub impl DebugSignedRay of Debug<SignedRay> {
    fn fmt(self: @SignedRay, ref f: Formatter) -> Result<(), Error> {
        Display::fmt(self, ref f)
    }
}

// Default
pub impl DefaultSignedWad of Default<SignedWad> {
    fn default() -> SignedWad {
        SignedWad { val: 0, sign: false }
    }
}

pub impl DefaultSignedRay of Default<SignedRay> {
    fn default() -> SignedRay {
        SignedRay { val: 0, sign: false }
    }
}

// Neg
pub impl SignedWadNeg of Neg<SignedWad> {
    fn neg(a: SignedWad) -> SignedWad {
        SignedWad { val: a.val, sign: !a.sign }
    }
}


pub impl SignedRayNeg of Neg<SignedRay> {
    fn neg(a: SignedRay) -> SignedRay {
        SignedRay { val: a.val, sign: !a.sign }
    }
}
