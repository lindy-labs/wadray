use integer::BoundedInt;
use math::Oneable;

const WAD_DECIMALS: u8 = 18;
const WAD_SCALE: u128 = 1000000000000000000;
const RAY_SCALE: u128 = 1000000000000000000000000000;
const WAD_ONE: u128 = 1000000000000000000;
const RAY_ONE: u128 = 1000000000000000000000000000;
const WAD_PERCENT: u128 = 10000000000000000;
const RAY_PERCENT: u128 = 10000000000000000000000000;

// Largest Wad that can be converted into a Ray without overflowing
// 2 ** 128 // DIFF
const MAX_CONVERTIBLE_WAD: u128 = 340282366920938463463374607431;

// The difference between WAD_SCALE and RAY_SCALE. RAY_SCALE = WAD_SCALE * DIFF
const DIFF: u128 = 1000000000;

#[derive(Copy, Drop, Serde, starknet::Store)]
struct Wad {
    val: u128,
}

#[derive(Copy, Drop, Serde, starknet::Store)]
struct Ray {
    val: u128
}

// Core functions

#[inline(always)]
fn cast_to_u256(a: u128, b: u128) -> (u256, u256) {
    (a.into(), b.into())
}

#[inline(always)]
fn wmul(lhs: Wad, rhs: Wad) -> Wad {
    Wad { val: wmul_internal(lhs.val, rhs.val) }
}

// wmul of Wad and Ray -> Ray
#[inline(always)]
fn wmul_wr(lhs: Wad, rhs: Ray) -> Ray {
    Ray { val: wmul_internal(lhs.val, rhs.val) }
}

#[inline(always)]
fn wmul_rw(lhs: Ray, rhs: Wad) -> Ray {
    wmul_wr(rhs, lhs)
}

#[inline(always)]
fn rmul(lhs: Ray, rhs: Ray) -> Ray {
    Ray { val: rmul_internal(lhs.val, rhs.val) }
}

// rmul of Wad and Ray -> Wad
#[inline(always)]
fn rmul_rw(lhs: Ray, rhs: Wad) -> Wad {
    Wad { val: rmul_internal(lhs.val, rhs.val) }
}

#[inline(always)]
fn rmul_wr(lhs: Wad, rhs: Ray) -> Wad {
    rmul_rw(rhs, lhs)
}

#[inline(always)]
fn wdiv(lhs: Wad, rhs: Wad) -> Wad {
    Wad { val: wdiv_internal(lhs.val, rhs.val) }
}

// wdiv of Ray by Wad -> Ray
#[inline(always)]
fn wdiv_rw(lhs: Ray, rhs: Wad) -> Ray {
    Ray { val: wdiv_internal(lhs.val, rhs.val) }
}

#[inline(always)]
fn rdiv(lhs: Ray, rhs: Ray) -> Ray {
    Ray { val: rdiv_internal(lhs.val, rhs.val) }
}

// rdiv of Wad by Ray -> Wad
#[inline(always)]
fn rdiv_wr(lhs: Wad, rhs: Ray) -> Wad {
    Wad { val: rdiv_internal(lhs.val, rhs.val) }
}

// rdiv of Wad by Wad -> Ray
#[inline(always)]
fn rdiv_ww(lhs: Wad, rhs: Wad) -> Ray {
    Ray { val: rdiv_internal(lhs.val, rhs.val) }
}

#[inline(always)]
fn scale_u128_by_ray(lhs: u128, rhs: Ray) -> u128 {
    rmul_internal(lhs, rhs.val)
}

#[inline(always)]
fn div_u128_by_ray(lhs: u128, rhs: Ray) -> u128 {
    rdiv_internal(lhs, rhs.val)
}

//
// Internal helpers
//

#[inline(always)]
fn wmul_internal(lhs: u128, rhs: u128) -> u128 {
    let (lhs_u256, rhs_u256) = cast_to_u256(lhs, rhs);
    (lhs_u256 * rhs_u256 / WAD_ONE.into()).try_into().expect('wmul_internal')
}

#[inline(always)]
fn rmul_internal(lhs: u128, rhs: u128) -> u128 {
    let (lhs_u256, rhs_u256) = cast_to_u256(lhs, rhs);
    (lhs_u256 * rhs_u256 / RAY_ONE.into()).try_into().expect('rmul_internal')
}

#[inline(always)]
fn wdiv_internal(lhs: u128, rhs: u128) -> u128 {
    let (lhs_u256, rhs_u256) = cast_to_u256(lhs, rhs);
    ((lhs_u256 * WAD_ONE.into()) / rhs_u256).try_into().expect('wdiv_internal')
}

#[inline(always)]
fn rdiv_internal(lhs: u128, rhs: u128) -> u128 {
    let (lhs_u256, rhs_u256) = cast_to_u256(lhs, rhs);
    ((lhs_u256 * RAY_ONE.into()) / rhs_u256).try_into().expect('rdiv_internal')
}


//
// Trait Implementations
//

// Addition
impl WadAdd of Add<Wad> {
    #[inline(always)]
    fn add(lhs: Wad, rhs: Wad) -> Wad {
        Wad { val: lhs.val + rhs.val }
    }
}

impl RayAdd of Add<Ray> {
    #[inline(always)]
    fn add(lhs: Ray, rhs: Ray) -> Ray {
        Ray { val: lhs.val + rhs.val }
    }
}

impl WadAddEq of AddEq<Wad> {
    #[inline(always)]
    fn add_eq(ref self: Wad, other: Wad) {
        self = self + other;
    }
}

impl RayAddEq of AddEq<Ray> {
    #[inline(always)]
    fn add_eq(ref self: Ray, other: Ray) {
        self = self + other;
    }
}


// Subtraction
impl WadSub of Sub<Wad> {
    #[inline(always)]
    fn sub(lhs: Wad, rhs: Wad) -> Wad {
        Wad { val: lhs.val - rhs.val }
    }
}

impl RaySub of Sub<Ray> {
    #[inline(always)]
    fn sub(lhs: Ray, rhs: Ray) -> Ray {
        Ray { val: lhs.val - rhs.val }
    }
}

impl WadSubEq of SubEq<Wad> {
    #[inline(always)]
    fn sub_eq(ref self: Wad, other: Wad) {
        self = self - other;
    }
}

impl RaySubEq of SubEq<Ray> {
    #[inline(always)]
    fn sub_eq(ref self: Ray, other: Ray) {
        self = self - other;
    }
}


// Multiplication
impl WadMul of Mul<Wad> {
    #[inline(always)]
    fn mul(lhs: Wad, rhs: Wad) -> Wad {
        wmul(lhs, rhs)
    }
}

impl RayMul of Mul<Ray> {
    #[inline(always)]
    fn mul(lhs: Ray, rhs: Ray) -> Ray {
        rmul(lhs, rhs)
    }
}

impl WadMulEq of MulEq<Wad> {
    #[inline(always)]
    fn mul_eq(ref self: Wad, other: Wad) {
        self = self * other;
    }
}

impl RayMulEq of MulEq<Ray> {
    #[inline(always)]
    fn mul_eq(ref self: Ray, other: Ray) {
        self = self * other;
    }
}


// Division
impl WadDiv of Div<Wad> {
    #[inline(always)]
    fn div(lhs: Wad, rhs: Wad) -> Wad {
        wdiv(lhs, rhs)
    }
}

impl RayDiv of Div<Ray> {
    #[inline(always)]
    fn div(lhs: Ray, rhs: Ray) -> Ray {
        rdiv(lhs, rhs)
    }
}

impl WadDivEq of DivEq<Wad> {
    #[inline(always)]
    fn div_eq(ref self: Wad, other: Wad) {
        self = self / other;
    }
}

impl RayDivEq of DivEq<Ray> {
    #[inline(always)]
    fn div_eq(ref self: Ray, other: Ray) {
        self = self / other;
    }
}


// Conversions
impl WadTryIntoRay of TryInto<Wad, Ray> {
    fn try_into(self: Wad) -> Option::<Ray> {
        if (self.val <= MAX_CONVERTIBLE_WAD) {
            Option::Some(Ray { val: self.val * DIFF })
        } else {
            Option::None
        }
    }
}

impl RayIntoWad of Into<Ray, Wad> {
    #[inline(always)]
    fn into(self: Ray) -> Wad {
        // The value will get truncated if it has more than 18 decimals.
        Wad { val: self.val / DIFF }
    }
}

impl TIntoWad<T, impl TIntoU128: Into<T, u128>> of Into<T, Wad> {
    #[inline(always)]
    fn into(self: T) -> Wad {
        Wad { val: self.into() }
    }
}

impl TIntoRay<T, impl TIntoU128: Into<T, u128>> of Into<T, Ray> {
    #[inline(always)]
    fn into(self: T) -> Ray {
        Ray { val: self.into() }
    }
}

impl WadIntoFelt252 of Into<Wad, felt252> {
    #[inline(always)]
    fn into(self: Wad) -> felt252 {
        self.val.into()
    }
}

impl WadIntoU256 of Into<Wad, u256> {
    #[inline(always)]
    fn into(self: Wad) -> u256 {
        self.val.into()
    }
}

impl RayIntoU256 of Into<Ray, u256> {
    #[inline(always)]
    fn into(self: Ray) -> u256 {
        self.val.into()
    }
}

impl U256TryIntoWad of TryInto<u256, Wad> {
    #[inline(always)]
    fn try_into(self: u256) -> Option<Wad> {
        match self.try_into() {
            Option::Some(val) => Option::Some(Wad { val }),
            Option::None => Option::None,
        }
    }
}

// Comparisons
impl WadPartialEq of PartialEq<Wad> {
    #[inline(always)]
    fn eq(lhs: @Wad, rhs: @Wad) -> bool {
        *lhs.val == *rhs.val
    }

    #[inline(always)]
    fn ne(lhs: @Wad, rhs: @Wad) -> bool {
        *lhs.val != *rhs.val
    }
}

impl RayPartialEq of PartialEq<Ray> {
    #[inline(always)]
    fn eq(lhs: @Ray, rhs: @Ray) -> bool {
        *lhs.val == *rhs.val
    }

    #[inline(always)]
    fn ne(lhs: @Ray, rhs: @Ray) -> bool {
        *lhs.val != *rhs.val
    }
}

impl WadPartialOrd of PartialOrd<Wad> {
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

impl RayPartialOrd of PartialOrd<Ray> {
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
impl BoundedWad of BoundedInt<Wad> {
    #[inline(always)]
    fn min() -> Wad nopanic {
        Wad { val: 0 }
    }

    #[inline(always)]
    fn max() -> Wad nopanic {
        Wad { val: integer::BoundedU128::max() }
    }
}

impl BoundedRay of BoundedInt<Ray> {
    #[inline(always)]
    fn min() -> Ray nopanic {
        Ray { val: 0 }
    }

    #[inline(always)]
    fn max() -> Ray nopanic {
        Ray { val: integer::BoundedU128::max() }
    }
}

// Zeroable
impl WadZeroable of Zeroable<Wad> {
    #[inline(always)]
    fn zero() -> Wad {
        Wad { val: 0 }
    }

    #[inline(always)]
    fn is_zero(self: Wad) -> bool {
        self.val == 0
    }

    #[inline(always)]
    fn is_non_zero(self: Wad) -> bool {
        self.val != 0
    }
}

impl RayZeroable of Zeroable<Ray> {
    #[inline(always)]
    fn zero() -> Ray {
        Ray { val: 0 }
    }

    #[inline(always)]
    fn is_zero(self: Ray) -> bool {
        self.val == 0
    }

    #[inline(always)]
    fn is_non_zero(self: Ray) -> bool {
        self.val != 0
    }
}

// Oneable

impl WadOneable of Oneable<Wad> {
    #[inline(always)]
    fn one() -> Wad {
        Wad { val: WAD_ONE }
    }

    #[inline(always)]
    fn is_one(self: Wad) -> bool {
        self.val == WAD_ONE
    }

    #[inline(always)]
    fn is_non_one(self: Wad) -> bool {
        self.val != WAD_ONE
    }
}

impl RayOneable of Oneable<Ray> {
    #[inline(always)]
    fn one() -> Ray {
        Ray { val: RAY_ONE }
    }

    #[inline(always)]
    fn is_one(self: Ray) -> bool {
        self.val == RAY_ONE
    }

    #[inline(always)]
    fn is_non_one(self: Ray) -> bool {
        self.val != RAY_ONE
    }
}

// Debug print
impl WadPrintImpl of debug::PrintTrait<Wad> {
    fn print(self: Wad) {
        self.val.print();
    }
}

impl RayPrintImpl of debug::PrintTrait<Ray> {
    fn print(self: Ray) {
        self.val.print();
    }
}