use core::fmt::{Debug, Display, DisplayInteger, Error, Formatter};
use core::num::traits::{One, Zero, Bounded};
use core::ops::{AddAssign, SubAssign, MulAssign, DivAssign};
use integer::{u256_safe_div_rem, u256_try_as_non_zero};
use starknet::StorePacking;
use wadray::wadray::{DIFF, Ray, RAY_ONE, u128_rdiv, u128_rmul, u128_wdiv, u128_wmul, Wad, WAD_ONE};

const HALF_PRIME: felt252 = 1809251394333065606848661391547535052811553607665798349986546028067936010240;

#[derive(Copy, Drop, Serde)]
struct SignedWad {
    val: u128,
    sign: bool
}

#[derive(Copy, Drop, Serde)]
struct SignedRay {
    val: u128,
    sign: bool
}

// External helpers
fn wad_to_signed_ray(a: Wad) -> SignedRay {
    SignedRay { val: a.val * DIFF, sign: false }
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
#[inline]
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
    lhs_sign ^ rhs_sign
}

fn _pack(val: u128, sign: bool) -> felt252 {
    // shift by 2**128
    let two_pow_128: felt252 = (Bounded::<u128>::MAX).into() + 1;
    val.into() + sign.into() * two_pow_128
}

fn _unpack(packed: felt252) -> (u128, bool) {
    let two_pow_128: u256 = (Bounded::<u128>::MAX).into() + 1; // 2**128
    let shift: NonZero<u256> = u256_try_as_non_zero(two_pow_128).unwrap();
    let (sign, val) = u256_safe_div_rem(packed.into(), shift);
    let val: u128 = val.try_into().expect('WadRay Signed val unpacking');
    let sign: u128 = sign.try_into().expect('WadRay Signed sign unpacking');
    (val, sign == 1)
}

//
// Trait Implementations
//

// StorePacking
impl SignedWadStorePacking of StorePacking<SignedWad, felt252> {
    fn pack(value: SignedWad) -> felt252 {
        _pack(value.val, value.sign)
    }

    fn unpack(value: felt252) -> SignedWad {
        let (val, sign) = _unpack(value);
        SignedWad { val, sign }
    }
}

impl SignedRayStorePacking of StorePacking<SignedRay, felt252> {
    fn pack(value: SignedRay) -> felt252 {
        _pack(value.val, value.sign)
    }

    fn unpack(value: felt252) -> SignedRay {
        let (val, sign) = _unpack(value);
        SignedRay { val, sign }
    }
}

// Addition
impl SignedWadAdd of Add<SignedWad> {
    fn add(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        signed_wad_from_felt(lhs.into() + rhs.into())
    }
}

impl SignedWadAddAsign of AddAssign<SignedWad, SignedWad> {
    #[inline]
    fn add_assign(ref self: SignedWad, rhs: SignedWad) {
        self = self + rhs;
    }
}

impl SignedRayAdd of Add<SignedRay> {
    fn add(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        signed_ray_from_felt(lhs.into() + rhs.into())
    }
}

impl SignedRayAddAssign of AddAssign<SignedRay, SignedRay> {
    #[inline]
    fn add_assign(ref self: SignedRay, rhs: SignedRay) {
        self = self + rhs;
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

impl SignedWadSubAssign of SubAssign<SignedWad, SignedWad> {
    #[inline]
    fn sub_assign(ref self: SignedWad, rhs: SignedWad) {
        self = self - rhs;
    }
}

impl SignedRaySubAssign of SubAssign<SignedRay, SignedRay> {
    #[inline]
    fn sub_assign(ref self: SignedRay, rhs: SignedRay) {
        self = self - rhs;
    }
}


// Multiplication
impl SignedWadMul of Mul<SignedWad> {
    fn mul(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = u128_wmul(lhs.val, rhs.val);
        SignedWad { val: val, sign: sign }
    }
}

impl SignedRayMul of Mul<SignedRay> {
    fn mul(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = u128_rmul(lhs.val, rhs.val);
        SignedRay { val: val, sign: sign }
    }
}

impl SignedWadMulAssign of MulAssign<SignedWad, SignedWad> {
    #[inline]
    fn mul_assign(ref self: SignedWad, rhs: SignedWad) {
        self = self * rhs;
    }
}

impl SignedRayMulAssign of MulAssign<SignedRay, SignedRay> {
    #[inline]
    fn mul_assign(ref self: SignedRay, rhs: SignedRay) {
        self = self * rhs;
    }
}


// Division
impl SignedWadDiv of Div<SignedWad> {
    fn div(lhs: SignedWad, rhs: SignedWad) -> SignedWad {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = u128_wdiv(lhs.val, rhs.val);
        SignedWad { val: val, sign: sign }
    }
}

impl SignedRayDiv of Div<SignedRay> {
    fn div(lhs: SignedRay, rhs: SignedRay) -> SignedRay {
        let sign = sign_from_mul(lhs.sign, rhs.sign);
        let val = u128_rdiv(lhs.val, rhs.val);
        SignedRay { val: val, sign: sign }
    }
}

impl SignedWadDivAssign of DivAssign<SignedWad, SignedWad> {
    #[inline]
    fn div_assign(ref self: SignedWad, rhs: SignedWad) {
        self = self / rhs;
    }
}

impl SignedRayDivAssign of DivAssign<SignedRay, SignedRay> {
    #[inline]
    fn div_assign(ref self: SignedRay, rhs: SignedRay) {
        self = self / rhs;
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

impl RayIntoSignedRay of Into<Ray, SignedRay> {
    fn into(self: Ray) -> SignedRay {
        SignedRay { val: self.val, sign: false }
    }
}

impl SignedWadTryIntoWad of TryInto<SignedWad, Wad> {
    fn try_into(self: SignedWad) -> Option<Wad> {
        if !self.sign || self.is_zero() {
            return Option::Some(Wad { val: self.val });
        } else {
            return Option::None;
        }
    }
}

impl SignedRayTryIntoRay of TryInto<SignedRay, Ray> {
    fn try_into(self: SignedRay) -> Option<Ray> {
        if !self.sign || self.is_zero() {
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

impl SignedWadPartialOrd of PartialOrd<SignedWad> {
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

impl SignedRayPartialEq of PartialEq<SignedRay> {
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

impl SignedRayPartialOrd of PartialOrd<SignedRay> {
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
impl BoundedSignedWad of Bounded<SignedWad> {
    const MAX: SignedWad = SignedWad { val: Bounded::MAX, sign: true };

    const MIN: SignedWad = SignedWad { val: Bounded::MAX, sign: false };
}

impl BoundedSignedRay of Bounded<SignedRay> {
    const MAX: SignedRay = SignedRay { val: Bounded::MAX, sign: true };

    const MIN: SignedRay = SignedRay { val: Bounded::MAX, sign: false };
}


// Zero
impl SignedWadZero of Zero<SignedWad> {
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

impl SignedRayZero of Zero<SignedRay> {
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
impl SignedWadOne of One<SignedWad> {
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

impl SignedRayOne of One<SignedRay> {
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


// Display and Debug
impl DisplaySignedWad of Display<SignedWad> {
    fn fmt(self: @SignedWad, ref f: Formatter) -> Result<(), Error> {
        if *self.sign {
            write!(f, "-")?;
        }

        Display::fmt(self.val, ref f)
    }
}

impl DisplaySignedRay of Display<SignedRay> {
    fn fmt(self: @SignedRay, ref f: Formatter) -> Result<(), Error> {
        if *self.sign {
            write!(f, "-")?;
        }

        Display::fmt(self.val, ref f)
    }
}

impl DebugSignedWad of Debug<SignedWad> {
    fn fmt(self: @SignedWad, ref f: Formatter) -> Result<(), Error> {
        Display::fmt(self, ref f)
    }
}

impl DebugSignedRay of Debug<SignedRay> {
    fn fmt(self: @SignedRay, ref f: Formatter) -> Result<(), Error> {
        Display::fmt(self, ref f)
    }
}
