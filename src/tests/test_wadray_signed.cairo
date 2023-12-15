mod test_wadray_signed {
    use debug::PrintTrait;
    use math::Oneable;
    use wadray::{
        BoundedSignedWad, BoundedSignedRay, Signed, SignedRay, SignedRayOneable, SignedRayZeroable, SignedWad,
        SignedWadOneable, SignedWadZeroable
    };
    use wadray::{DIFF, Ray, RAY_ONE, Wad, WAD_ONE};

    #[test]
    fn test_add_sub() {
        let a = SignedWad { val: 100, sign: false };
        let b = SignedWad { val: 100, sign: true };
        let c = SignedWad { val: 40, sign: true };

        assert(a + b == SignedWadZeroable::zero(), 'a + b != 0');
        assert(a - b == SignedWad { val: 200, sign: false }, 'a - b != 200');
        assert(b - a == SignedWad { val: 200, sign: true }, 'b - a != -200');
        assert(a + c == SignedWad { val: 60, sign: false }, 'a + c != 60');
        assert(a - c == SignedWad { val: 140, sign: false }, 'a - c != 140');

        let a = SignedRay { val: 100, sign: false };
        let b = SignedRay { val: 100, sign: true };
        let c = SignedRay { val: 40, sign: true };

        assert(a + b == SignedRayZeroable::zero(), 'a + b != 0');
        assert(a - b == SignedRay { val: 200, sign: false }, 'a - b != 200');
        assert(b - a == SignedRay { val: 200, sign: true }, 'b - a != -200');
        assert(a + c == SignedRay { val: 60, sign: false }, 'a + c != 60');
        assert(a - c == SignedRay { val: 140, sign: false }, 'a - c != 140');
    }

    #[test]
    fn test_add_eq() {
        let mut a1 = SignedWad { val: 5, sign: true };
        let a2 = SignedWad { val: 5, sign: true };
        let b = SignedWad { val: 3, sign: false };

        a1 += b;
        assert(a1 == a2 + b, 'Incorrect AddEq #1');
    }

    #[test]
    fn test_sub_eq() {
        let mut a1 = SignedWad { val: 5, sign: true };
        let a2 = SignedWad { val: 5, sign: true };
        let b = SignedWad { val: 3, sign: false };

        a1 -= b;
        assert(a1 == a2 - b, 'Incorrect SubEq #1');
    }

    #[test]
    fn test_mul_div() {
        let a = SignedWad { val: WAD_ONE, sign: false }; // 1.0 ray
        let b = SignedWad { val: 2 * WAD_ONE, sign: true }; // -2.0 ray
        let c = SignedWad { val: 5 * WAD_ONE, sign: false }; // 5.0 ray
        let d = SignedWad { val: WAD_ONE, sign: true }; // -1.0 ray

        // Test multiplication
        assert((a * b) == SignedWad { val: 2 * WAD_ONE, sign: true }, 'a * b != -2.0');
        assert((a * c) == SignedWad { val: 5 * WAD_ONE, sign: false }, 'a * c != 5.0');
        assert((b * c) == SignedWad { val: 10 * WAD_ONE, sign: true }, 'b * c != -10.0');

        // Test division
        assert((c / a) == SignedWad { val: 5 * WAD_ONE, sign: false }, 'c / a != 5.0');
        assert((a / d) == SignedWad { val: 1 * WAD_ONE, sign: true }, 'a / d != -1.0');
        assert((b / d) == SignedWad { val: 2 * WAD_ONE, sign: false }, 'b / d != 2.0');

        let a = SignedRay { val: RAY_ONE, sign: false }; // 1.0 ray
        let b = SignedRay { val: 2 * RAY_ONE, sign: true }; // -2.0 ray
        let c = SignedRay { val: 5 * RAY_ONE, sign: false }; // 5.0 ray
        let d = SignedRay { val: RAY_ONE, sign: true }; // -1.0 ray

        // Test multiplication
        assert((a * b) == SignedRay { val: 2 * RAY_ONE, sign: true }, 'a * b != -2.0');
        assert((a * c) == SignedRay { val: 5 * RAY_ONE, sign: false }, 'a * c != 5.0');
        assert((b * c) == SignedRay { val: 10 * RAY_ONE, sign: true }, 'b * c != -10.0');

        // Test division
        assert((c / a) == SignedRay { val: 5 * RAY_ONE, sign: false }, 'c / a != 5.0');
        assert((a / d) == SignedRay { val: 1 * RAY_ONE, sign: true }, 'a / d != -1.0');
        assert((b / d) == SignedRay { val: 2 * RAY_ONE, sign: false }, 'b / d != 2.0');
    }

    #[test]
    fn test_mul_eq() {
        let mut a1 = SignedWad { val: 5, sign: true };
        let a2 = SignedWad { val: 5, sign: true };
        let b = SignedWad { val: 3, sign: false };

        a1 *= b;
        assert(a1 == a2 * b, 'Incorrect MulEq #1');
    }

    #[test]
    fn test_div_eq() {
        let mut a1 = SignedWad { val: 15, sign: true };
        let a2 = SignedWad { val: 15, sign: true };
        let b = SignedWad { val: 3, sign: false };

        a1 /= b;
        assert(a1 == a2 / b, 'Incorrect DivEq #1');
    }

    #[test]
    fn test_comparison() {
        let a = SignedWad { val: 100, sign: false };
        let b = SignedWad { val: 100, sign: true };
        let c = SignedWad { val: 40, sign: true };
        let d = SignedWad { val: 40, sign: false };
        let zero = SignedWad { val: 0, sign: false };

        // Test greater than operator
        assert(a > b, 'a > b');
        assert(a > c, 'a > c');
        assert(!(b > a), 'b > a');
        assert(!(c > a), 'c > a');
        assert(!(zero > a), '0 > a');
        assert(a > zero, 'a > 0');

        // Test less than operator
        assert(b < a, 'b < a');
        assert(c < a, 'c < a');
        assert(!(a < b), 'a < b');
        assert(!(a < c), 'a < c');
        assert(zero < a, '0 < a');
        assert(!(a < zero), 'a < 0');

        // Test greater than or equal to operator
        assert(a >= b, 'a >= b');
        assert(a >= d, 'a >= d');
        assert(!(b >= a), 'b >= a');
        assert(c >= c, 'c >= c');
        assert(zero >= zero, '0 >= 0');
        assert(a >= zero, 'a >= 0');
        assert(!(zero >= a), '0 >= a');

        // Test less than or equal to operator
        assert(b <= a, 'b <= a');
        assert(d <= a, 'd <= a');
        assert(!(a <= b), 'a <= b');
        assert(c <= c, 'c <= c');
        assert(zero <= zero, '0 <= 0');
        assert(zero <= a, '0 <= a');
        assert(!(a <= zero), 'a <= 0');

        let a = SignedRay { val: 100, sign: false };
        let b = SignedRay { val: 100, sign: true };
        let c = SignedRay { val: 40, sign: true };
        let d = SignedRay { val: 40, sign: false };
        let zero = SignedRay { val: 0, sign: false };

        // Test greater than operator
        assert(a > b, 'a > b');
        assert(a > c, 'a > c');
        assert(!(b > a), 'b > a');
        assert(!(c > a), 'c > a');
        assert(!(zero > a), '0 > a');
        assert(a > zero, 'a > 0');

        // Test less than operator
        assert(b < a, 'b < a');
        assert(c < a, 'c < a');
        assert(!(a < b), 'a < b');
        assert(!(a < c), 'a < c');
        assert(zero < a, '0 < a');
        assert(!(a < zero), 'a < 0');

        // Test greater than or equal to operator
        assert(a >= b, 'a >= b');
        assert(a >= d, 'a >= d');
        assert(!(b >= a), 'b >= a');
        assert(c >= c, 'c >= c');
        assert(zero >= zero, '0 >= 0');
        assert(a >= zero, 'a >= 0');
        assert(!(zero >= a), '0 >= a');

        // Test less than or equal to operator
        assert(b <= a, 'b <= a');
        assert(d <= a, 'd <= a');
        assert(!(a <= b), 'a <= b');
        assert(c <= c, 'c <= c');
        assert(zero <= zero, '0 <= 0');
        assert(zero <= a, '0 <= a');
        assert(!(a <= zero), 'a <= 0');
    }

    #[test]
    fn test_bounded() {
        let max_u128 = 0xffffffffffffffffffffffffffffffff;

        assert(BoundedSignedWad::min() == SignedWad { val: max_u128, sign: true }, 'SignedWad min');
        assert(BoundedSignedWad::max() == SignedWad { val: max_u128, sign: false }, 'SignedWad max');

        assert(BoundedSignedRay::min() == SignedRay { val: max_u128, sign: true }, 'SignedRay min');
        assert(BoundedSignedRay::max() == SignedRay { val: max_u128, sign: false }, 'SignedRay max');
    }

    #[test]
    fn test_into_conversions() {
        // Test U128IntoSignedWad
        let a: u128 = 100;
        let a_signed: SignedWad = a.into();
        assert(a_signed.val == a, 'U128IntoSignedWad val fail');
        assert(!a_signed.sign, 'U128IntoSignedWad sign fail');

        // Test WadIntoSignedWad
        let b = Wad { val: 200 };
        let b_signed: SignedWad = b.into();
        assert(b_signed.val == b.val, 'WadIntoSignedWad val fail');
        assert(!b_signed.sign, 'WadIntoSignedWad sign fail');

        // Test SignedWadTryIntoWad
        let d = SignedWad { val: 400, sign: false };
        let d_wad: Option<Wad> = d.try_into();
        assert(d_wad.is_some(), 'SignedWadTryIntoWad pos fail');
        assert(d_wad.unwrap().val == d.val, 'SignedWadTryIntoWad val fail');

        let e = SignedWad { val: 500, sign: true };
        let e_wad: Option<Wad> = e.try_into();
        assert(e_wad.is_none(), 'SignedWadTryIntoWad neg fail');

        // Test U128IntoSignedRay
        let a: u128 = 100;
        let a_signed: SignedRay = a.into();
        assert(a_signed.val == a, 'U128IntoSignedRay val fail');
        assert(!a_signed.sign, 'U128IntoSignedRay sign fail');

        // Test RayIntoSignedRay
        let b = Ray { val: 200 };
        let b_signed: SignedRay = b.into();
        assert(b_signed.val == b.val, 'RayIntoSignedRay val fail');
        assert(!b_signed.sign, 'RayIntoSignedRay sign fail');

        // Test WadIntoSignedRay
        let c = Wad { val: 300 * WAD_ONE };
        let c_signed: SignedRay = c.into();
        assert(c_signed.val == c.val * DIFF, 'WadIntoSignedRay val fail');
        assert(!c_signed.sign, 'WadIntoSignedRay sign fail');

        // Test SignedRayTryIntoRay
        let d = SignedRay { val: 400, sign: false };
        let d_ray: Option<Ray> = d.try_into();
        assert(d_ray.is_some(), 'SignedRayTryIntoRay pos fail');
        assert(d_ray.unwrap().val == d.val, 'SignedRayTryIntoRay val fail');

        let e = SignedRay { val: 500, sign: true };
        let e_ray: Option<Ray> = e.try_into();
        assert(e_ray.is_none(), 'SignedRayTryIntoRay neg fail');
    }

    #[test]
    fn test_zeroable_oneable() {
        // Test SignedWadZeroable
        let zero = SignedWadZeroable::zero();
        assert(zero.val == 0, 'Zeroable zero fail');
        assert(!zero.sign, 'Zeroable zero sign fail');
        assert(zero.is_zero(), 'Zeroable is_zero fail');
        assert(!zero.is_non_zero(), 'Zeroable is_non_zero fail');

        let non_zero = SignedWad { val: 100, sign: false };
        assert(!non_zero.is_zero(), 'Zeroable non_zero fail');
        assert(non_zero.is_non_zero(), 'Zeroable non_zero fail');

        // Test SignedWadOneable
        let one = SignedWadOneable::one();
        assert(one.val == WAD_ONE, 'Oneable one fail');
        assert(!one.sign, 'Oneable one sign fail');
        assert(one.is_one(), 'Oneable is_one fail');
        assert(!one.is_non_one(), 'Oneable is_non_one fail');

        let non_one = SignedWad { val: 200, sign: false };
        assert(!non_one.is_one(), 'Oneable non_one fail');
        assert(non_one.is_non_one(), 'Oneable non_one fail');

        // Test SignedRayZeroable
        let zero = SignedRayZeroable::zero();
        assert(zero.val == 0, 'Zeroable zero fail');
        assert(!zero.sign, 'Zeroable zero sign fail');
        assert(zero.is_zero(), 'Zeroable is_zero fail');
        assert(!zero.is_non_zero(), 'Zeroable is_non_zero fail');

        let non_zero = SignedRay { val: 100, sign: false };
        assert(!non_zero.is_zero(), 'Zeroable non_zero fail');
        assert(non_zero.is_non_zero(), 'Zeroable non_zero fail');

        // Test SignedRayOneable
        let one = SignedRayOneable::one();
        assert(one.val == RAY_ONE, 'Oneable one fail');
        assert(!one.sign, 'Oneable one sign fail');
        assert(one.is_one(), 'Oneable is_one fail');
        assert(!one.is_non_one(), 'Oneable is_non_one fail');

        let non_one = SignedRay { val: 200, sign: false };
        assert(!non_one.is_one(), 'Oneable non_one fail');
        assert(non_one.is_non_one(), 'Oneable non_one fail');
    }

    #[test]
    fn test_signed() {
        // Test SignedWadSigned
        let zero = SignedWadZeroable::zero();
        let one = SignedWad { val: 1, sign: false };
        let neg_one = SignedWad { val: 1, sign: true };

        assert(!zero.is_positive() && !zero.is_negative(), 'Signed zero fail');
        assert(one.is_positive() && !one.is_negative(), 'Signed one fail');
        assert(!neg_one.is_positive() && neg_one.is_negative(), 'Signed neg one fail');

        // Test SignedRaySigned
        let zero = SignedRayZeroable::zero();
        let one = SignedRay { val: 1, sign: false };
        let neg_one = SignedRay { val: 1, sign: true };

        assert(!zero.is_positive() && !zero.is_negative(), 'Signed zero fail');
        assert(one.is_positive() && !one.is_negative(), 'Signed one fail');
        assert(!neg_one.is_positive() && neg_one.is_negative(), 'Signed neg one fail');
    }

    #[test]
    fn test_zero_cmp() {
        let pos_zero = SignedWad { val: 0, sign: false };
        let neg_zero = SignedWad { val: 0, sign: true };

        assert(pos_zero == neg_zero, 'Zero eq');
        assert(!(pos_zero != neg_zero), 'Zero neq');
        assert(pos_zero >= neg_zero, 'Zero ge');
        assert(pos_zero <= neg_zero, 'Zero le');
        assert(!(pos_zero > neg_zero), 'Zero gt');
        assert(!(pos_zero < neg_zero), 'Zero lt');

        let pos_zero = SignedRay { val: 0, sign: false };
        let neg_zero = SignedRay { val: 0, sign: true };

        assert(pos_zero == neg_zero, 'Zero eq');
        assert(!(pos_zero != neg_zero), 'Zero neq');
        assert(pos_zero >= neg_zero, 'Zero ge');
        assert(pos_zero <= neg_zero, 'Zero le');
        assert(!(pos_zero > neg_zero), 'Zero gt');
        assert(!(pos_zero < neg_zero), 'Zero lt');
    }
}
