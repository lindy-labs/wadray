use core::fmt::{Debug, Display, Error, Formatter};
use core::num::traits::{One, Zero, Bounded};
use core::ops::{AddAssign, SubAssign, MulAssign, DivAssign};


pub const WAD_DECIMALS: u8 = 18;
pub const WAD_SCALE: u128 = 1000000000000000000;
pub const RAY_SCALE: u128 = 1000000000000000000000000000;
pub const WAD_ONE: u128 = 1000000000000000000;
pub const RAY_ONE: u128 = 1000000000000000000000000000;
pub const WAD_PERCENT: u128 = 10000000000000000;
pub const RAY_PERCENT: u128 = 10000000000000000000000000;

// Largest Wad that can be converted into a Ray without overflowing
// 2 ** 128 // DIFF
pub(crate) const MAX_CONVERTIBLE_WAD: u128 = 340282366920938463463374607431;

// The difference between WAD_SCALE and RAY_SCALE. RAY_SCALE = WAD_SCALE * DIFF
pub(crate) const DIFF: u128 = 1000000000;

#[derive(Copy, Drop, Serde, starknet::Store)]
pub struct Wad {
    pub(crate) val: u128,
}

#[derive(Copy, Drop, Serde, starknet::Store)]
pub struct Ray {
    pub(crate) val: u128
}

// Core functions

#[inline]
pub fn wmul(lhs: Wad, rhs: Wad) -> Wad {
    Wad { val: u128_wmul(lhs.val, rhs.val) }
}

// wmul of Wad and Ray -> Ray
#[inline]
pub fn wmul_wr(lhs: Wad, rhs: Ray) -> Ray {
    Ray { val: u128_wmul(lhs.val, rhs.val) }
}

#[inline]
pub fn wmul_rw(lhs: Ray, rhs: Wad) -> Ray {
    wmul_wr(rhs, lhs)
}

#[inline]
pub fn rmul(lhs: Ray, rhs: Ray) -> Ray {
    Ray { val: u128_rmul(lhs.val, rhs.val) }
}

// rmul of Wad and Ray -> Wad
#[inline]
pub fn rmul_rw(lhs: Ray, rhs: Wad) -> Wad {
    Wad { val: u128_rmul(lhs.val, rhs.val) }
}

#[inline]
pub fn rmul_wr(lhs: Wad, rhs: Ray) -> Wad {
    rmul_rw(rhs, lhs)
}

#[inline]
pub fn wdiv(lhs: Wad, rhs: Wad) -> Wad {
    Wad { val: u128_wdiv(lhs.val, rhs.val) }
}

// wdiv of Ray by Wad -> Ray
#[inline]
pub fn wdiv_rw(lhs: Ray, rhs: Wad) -> Ray {
    Ray { val: u128_wdiv(lhs.val, rhs.val) }
}

#[inline]
pub fn rdiv(lhs: Ray, rhs: Ray) -> Ray {
    Ray { val: u128_rdiv(lhs.val, rhs.val) }
}

// rdiv of Wad by Ray -> Wad
#[inline]
pub fn rdiv_wr(lhs: Wad, rhs: Ray) -> Wad {
    Wad { val: u128_rdiv(lhs.val, rhs.val) }
}

// rdiv of Wad by Wad -> Ray
#[inline]
pub fn rdiv_ww(lhs: Wad, rhs: Wad) -> Ray {
    Ray { val: u128_rdiv(lhs.val, rhs.val) }
}

#[inline]
pub fn scale_u128_by_ray(lhs: u128, rhs: Ray) -> u128 {
    u128_rmul(lhs, rhs.val)
}

#[inline]
pub fn div_u128_by_ray(lhs: u128, rhs: Ray) -> u128 {
    u128_rdiv(lhs, rhs.val)
}

//
// Helpers
//

#[inline]
pub(crate) fn u128_wmul(lhs: u128, rhs: u128) -> u128 {
    let res: u256 = lhs.into() * rhs.into() / WAD_ONE.into();
    res.try_into().expect('u128_wmul')
}

#[inline]
pub(crate) fn u128_rmul(lhs: u128, rhs: u128) -> u128 {
    let res: u256 = lhs.into() * rhs.into() / RAY_ONE.into();
    res.try_into().expect('u128_rmul')
}

#[inline]
pub(crate) fn u128_wdiv(lhs: u128, rhs: u128) -> u128 {
    let res: u256 = lhs.into() * WAD_ONE.into() / rhs.into();
    res.try_into().expect('u128_wdiv')
}

#[inline]
pub(crate) fn u128_rdiv(lhs: u128, rhs: u128) -> u128 {
    let res: u256 = lhs.into() * RAY_ONE.into() / rhs.into();
    res.try_into().expect('u128_rdiv')
}


//
// Trait Implementations
//

// Addition
pub impl WadAdd of Add<Wad> {
    #[inline]
    fn add(lhs: Wad, rhs: Wad) -> Wad {
        Wad { val: lhs.val + rhs.val }
    }
}

pub impl RayAdd of Add<Ray> {
    #[inline]
    fn add(lhs: Ray, rhs: Ray) -> Ray {
        Ray { val: lhs.val + rhs.val }
    }
}

pub impl WadAddAssign of AddAssign<Wad, Wad> {
    #[inline]
    fn add_assign(ref self: Wad, rhs: Wad) {
        self = self + rhs;
    }
}

pub impl RayAddAssign of AddAssign<Ray, Ray> {
    #[inline]
    fn add_assign(ref self: Ray, rhs: Ray) {
        self = self + rhs;
    }
}


// Subtraction
pub impl WadSub of Sub<Wad> {
    #[inline]
    fn sub(lhs: Wad, rhs: Wad) -> Wad {
        Wad { val: lhs.val - rhs.val }
    }
}

pub impl RaySub of Sub<Ray> {
    #[inline]
    fn sub(lhs: Ray, rhs: Ray) -> Ray {
        Ray { val: lhs.val - rhs.val }
    }
}

pub impl WadSubAssign of SubAssign<Wad, Wad> {
    #[inline]
    fn sub_assign(ref self: Wad, rhs: Wad) {
        self = self - rhs;
    }
}

pub  impl RaySubAssign of SubAssign<Ray, Ray> {
    #[inline]
    fn sub_assign(ref self: Ray, rhs: Ray) {
        self = self - rhs;
    }
}


// Multiplication
pub impl WadMul of Mul<Wad> {
    #[inline]
    fn mul(lhs: Wad, rhs: Wad) -> Wad {
        wmul(lhs, rhs)
    }
}

pub impl RayMul of Mul<Ray> {
    #[inline]
    fn mul(lhs: Ray, rhs: Ray) -> Ray {
        rmul(lhs, rhs)
    }
}

pub impl WadMulAssign of MulAssign<Wad, Wad> {
    #[inline]
    fn mul_assign(ref self: Wad, rhs: Wad) {
        self = self * rhs;
    }
}

pub impl RayMulAssign of MulAssign<Ray, Ray> {
    #[inline]
    fn mul_assign(ref self: Ray, rhs: Ray) {
        self = self * rhs;
    }
}


// Division
pub impl WadDiv of Div<Wad> {
    #[inline]
    fn div(lhs: Wad, rhs: Wad) -> Wad {
        wdiv(lhs, rhs)
    }
}

pub impl RayDiv of Div<Ray> {
    #[inline]
    fn div(lhs: Ray, rhs: Ray) -> Ray {
        rdiv(lhs, rhs)
    }
}

pub impl WadDivAssign of DivAssign<Wad, Wad> {
    #[inline]
    fn div_assign(ref self: Wad, rhs: Wad) {
        self = self / rhs;
    }
}

pub impl RayDivAssign of DivAssign<Ray, Ray> {
    #[inline]
    fn div_assign(ref self: Ray, rhs: Ray) {
        self = self / rhs;
    }
}


// Conversions
pub impl WadTryIntoRay of TryInto<Wad, Ray> {
    fn try_into(self: Wad) -> Option::<Ray> {
        if (self.val <= MAX_CONVERTIBLE_WAD) {
            Option::Some(Ray { val: self.val * DIFF })
        } else {
            Option::None
        }
    }
}

// Truncates a ray into a wad.
pub fn ray_to_wad(x: Ray) -> Wad {
    Wad { val: x.val / DIFF }
}

pub impl TIntoWad<T, impl TIntoU128: Into<T, u128>> of Into<T, Wad> {
    #[inline]
    fn into(self: T) -> Wad {
        Wad { val: self.into() }
    }
}

pub impl TIntoRay<T, impl TIntoU128: Into<T, u128>> of Into<T, Ray> {
    #[inline]
    fn into(self: T) -> Ray {
        Ray { val: self.into() }
    }
}

pub impl WadIntoFelt252 of Into<Wad, felt252> {
    #[inline]
    fn into(self: Wad) -> felt252 {
        self.val.into()
    }
}

pub impl WadIntoU256 of Into<Wad, u256> {
    #[inline]
    fn into(self: Wad) -> u256 {
        self.val.into()
    }
}

pub impl RayIntoU256 of Into<Ray, u256> {
    #[inline]
    fn into(self: Ray) -> u256 {
        self.val.into()
    }
}

pub impl U256TryIntoWad of TryInto<u256, Wad> {
    #[inline]
    fn try_into(self: u256) -> Option<Wad> {
        match self.try_into() {
            Option::Some(val) => Option::Some(Wad { val }),
            Option::None => Option::None,
        }
    }
}

// Comparisons
pub impl WadPartialEq of PartialEq<Wad> {
    #[inline]
    fn eq(lhs: @Wad, rhs: @Wad) -> bool {
        *lhs.val == *rhs.val
    }

    #[inline]
    fn ne(lhs: @Wad, rhs: @Wad) -> bool {
        *lhs.val != *rhs.val
    }
}

pub impl RayPartialEq of PartialEq<Ray> {
    #[inline]
    fn eq(lhs: @Ray, rhs: @Ray) -> bool {
        *lhs.val == *rhs.val
    }

    #[inline]
    fn ne(lhs: @Ray, rhs: @Ray) -> bool {
        *lhs.val != *rhs.val
    }
}

pub impl WadPartialOrd of PartialOrd<Wad> {
    fn le(lhs: Wad, rhs: Wad) -> bool {
        lhs.val <= rhs.val
    }

    fn ge(lhs: Wad, rhs: Wad) -> bool {
        lhs.val >= rhs.val
    }

    fn lt(lhs: Wad, rhs: Wad) -> bool {
        lhs.val < rhs.val
    }

    fn gt(lhs: Wad, rhs: Wad) -> bool {
        lhs.val > rhs.val
    }
}

pub impl RayPartialOrd of PartialOrd<Ray> {
    fn le(lhs: Ray, rhs: Ray) -> bool {
        lhs.val <= rhs.val
    }

    fn ge(lhs: Ray, rhs: Ray) -> bool {
        lhs.val >= rhs.val
    }

    fn lt(lhs: Ray, rhs: Ray) -> bool {
        lhs.val < rhs.val
    }

    fn gt(lhs: Ray, rhs: Ray) -> bool {
        lhs.val > rhs.val
    }
}

// Bounded
pub impl BoundedWad of Bounded<Wad> {
    const MIN: Wad = Wad { val: 0 };

    const MAX: Wad = Wad { val: Bounded::MAX };
}

pub impl BoundedRay of Bounded<Ray> {
    const MIN: Ray = Ray { val: 0 };

    const MAX: Ray = Ray { val: Bounded::MAX };
}

// Zero
pub impl WadZero of Zero<Wad> {
    #[inline]
    fn zero() -> Wad {
        Wad { val: 0 }
    }

    #[inline]
    fn is_zero(self: @Wad) -> bool {
        *self.val == 0
    }

    #[inline]
    fn is_non_zero(self: @Wad) -> bool {
        *self.val != 0
    }
}

pub impl RayZero of Zero<Ray> {
    #[inline]
    fn zero() -> Ray {
        Ray { val: 0 }
    }

    #[inline]
    fn is_zero(self: @Ray) -> bool {
        *self.val == 0
    }

    #[inline]
    fn is_non_zero(self: @Ray) -> bool {
        *self.val != 0
    }
}

// One
pub impl WadOne of One<Wad> {
    #[inline]
    fn one() -> Wad {
        Wad { val: WAD_ONE }
    }

    #[inline]
    fn is_one(self: @Wad) -> bool {
        *self.val == WAD_ONE
    }

    #[inline]
    fn is_non_one(self: @Wad) -> bool {
        *self.val != WAD_ONE
    }
}

pub impl RayOne of One<Ray> {
    #[inline]
    fn one() -> Ray {
        Ray { val: RAY_ONE }
    }

    #[inline]
    fn is_one(self: @Ray) -> bool {
        *self.val == RAY_ONE
    }

    #[inline]
    fn is_non_one(self: @Ray) -> bool {
        *self.val != RAY_ONE
    }
}

// Display and Debug
pub impl DisplayWad of Display<Wad> {
    fn fmt(self: @Wad, ref f: Formatter) -> Result<(), Error> {
        Display::fmt(self.val, ref f)
    }
}

pub impl DisplayRay of Display<Ray> {
    fn fmt(self: @Ray, ref f: Formatter) -> Result<(), Error> {
        Display::fmt(self.val, ref f)
    }
}

pub impl DebugWad of Debug<Wad> {
    fn fmt(self: @Wad, ref f: Formatter) -> Result<(), Error> {
        Display::fmt(self, ref f)
    }
}

pub impl DebugRay of Debug<Ray> {
    fn fmt(self: @Ray, ref f: Formatter) -> Result<(), Error> {
        Display::fmt(self, ref f)
    }
}
