mod test_wadray_signed {
    use debug::PrintTrait;
    use math::Oneable;
    use wadray::{
        BoundedSignedWad, BoundedSignedRay, DIFF, Ray, RAY_ONE, Signed, SignedRay, SignedRayOneable, SignedRayZeroable,
        SignedWad, SignedWadOneable, SignedWadZeroable, Wad, WAD_ONE
    };

    #[test]
    fn test_add_sub() {
        let a = SignedWad { val: 100, sign: false };
        let b = SignedWad { val: 100, sign: true };
        let c = SignedWad { val: 40, sign: true };

        assert_eq!(a + b, SignedWadZeroable::zero(), "a + b != 0");
        assert_eq!(a - b, SignedWad { val: 200, sign: false }, "a - b != 200");
        assert_eq!(b - a, SignedWad { val: 200, sign: true }, "b - a != -200");
        assert_eq!(a + c, SignedWad { val: 60, sign: false }, "a + c != 60");
        assert_eq!(a - c, SignedWad { val: 140, sign: false }, "a - c != 140");

        let a = SignedRay { val: 100, sign: false };
        let b = SignedRay { val: 100, sign: true };
        let c = SignedRay { val: 40, sign: true };

        assert_eq!(a + b, SignedRayZeroable::zero(), "a + b != 0");
        assert_eq!(a - b, SignedRay { val: 200, sign: false }, "a - b != 200");
        assert_eq!(b - a, SignedRay { val: 200, sign: true }, "b - a != -200");
        assert_eq!(a + c, SignedRay { val: 60, sign: false }, "a + c != 60");
        assert_eq!(a - c, SignedRay { val: 140, sign: false }, "a - c != 140");
    }

    #[test]
    fn test_add_eq() {
        let mut a1 = SignedWad { val: 5, sign: true };
        let a2 = SignedWad { val: 5, sign: true };
        let b = SignedWad { val: 3, sign: false };

        a1 += b;
        assert_eq!(a1, a2 + b, "Incorrect AddEq #1");

        let mut a1 = SignedRay { val: 5, sign: true };
        let a2 = SignedRay { val: 5, sign: true };
        let b = SignedRay { val: 3, sign: false };

        a1 += b;
        assert_eq!(a1, a2 + b, "Incorrect AddEq #2");
    }

    #[test]
    fn test_sub_eq() {
        let mut a1 = SignedWad { val: 5, sign: true };
        let a2 = SignedWad { val: 5, sign: true };
        let b = SignedWad { val: 3, sign: false };

        a1 -= b;
        assert_eq!(a1, a2 - b, "Incorrect SubEq #1");

        let mut a1 = SignedRay { val: 5, sign: true };
        let a2 = SignedRay { val: 5, sign: true };
        let b = SignedRay { val: 3, sign: false };

        a1 -= b;
        assert_eq!(a1, a2 - b, "Incorrect SubEq #2");
    }

    #[test]
    fn test_mul_div() {
        let a = SignedWad { val: WAD_ONE, sign: false }; // 1.0 wad
        let b = SignedWad { val: 2 * WAD_ONE, sign: true }; // -2.0 wad
        let c = SignedWad { val: 5 * WAD_ONE, sign: false }; // 5.0 wad
        let d = SignedWad { val: WAD_ONE, sign: true }; // -1.0 wad

        // Test multiplication
        assert_eq!((a * b), SignedWad { val: 2 * WAD_ONE, sign: true }, "a * b != -2.0");
        assert_eq!((a * c), SignedWad { val: 5 * WAD_ONE, sign: false }, "a * c != 5.0");
        assert_eq!((b * c), SignedWad { val: 10 * WAD_ONE, sign: true }, "b * c != -10.0");
        assert_eq!((a * d), d, "a * d != -1.0");

        // Test division
        assert_eq!((c / a), SignedWad { val: 5 * WAD_ONE, sign: false }, "c / a != 5.0");
        assert_eq!((a / d), SignedWad { val: 1 * WAD_ONE, sign: true }, "a / d != -1.0");
        assert_eq!((b / d), SignedWad { val: 2 * WAD_ONE, sign: false }, "b / d != 2.0");
        assert_eq!((a / d), d, "a / d != -1.0");

        let a = SignedRay { val: RAY_ONE, sign: false }; // 1.0 ray
        let b = SignedRay { val: 2 * RAY_ONE, sign: true }; // -2.0 ray
        let c = SignedRay { val: 5 * RAY_ONE, sign: false }; // 5.0 ray
        let d = SignedRay { val: RAY_ONE, sign: true }; // -1.0 ray

        // Test multiplication
        assert_eq!((a * b), SignedRay { val: 2 * RAY_ONE, sign: true }, "a * b != -2.0");
        assert_eq!((a * c), SignedRay { val: 5 * RAY_ONE, sign: false }, "a * c != 5.0");
        assert_eq!((b * c), SignedRay { val: 10 * RAY_ONE, sign: true }, "b * c != -10.0");
        assert_eq!((a * d), d, "a * d != -1.0");

        // Test division
        assert_eq!((c / a), SignedRay { val: 5 * RAY_ONE, sign: false }, "c / a != 5.0");
        assert_eq!((a / d), SignedRay { val: 1 * RAY_ONE, sign: true }, "a / d != -1.0");
        assert_eq!((b / d), SignedRay { val: 2 * RAY_ONE, sign: false }, "b / d != 2.0");
        assert_eq!((a / d), d, "a / d != -1.0");
    }

    #[test]
    fn test_zero_mul() {
        let zero = SignedWad { val: 0, sign: false };
        let neg_zero = SignedWad { val: 0, sign: true };
        let one = SignedWad { val: WAD_ONE, sign: false }; // 1.0 wad
        let neg_one = SignedWad { val: WAD_ONE, sign: true }; // -1.0 wad

        assert_eq!((one * zero), SignedWadZeroable::zero(), "SignedWad zero mul #1");
        assert_eq!((neg_one * zero), SignedWadZeroable::zero(), "SignedWad zero mul #2");
        assert_eq!((one * neg_zero), SignedWadZeroable::zero(), "SignedWad zero mul #3");
        assert_eq!((neg_one * neg_zero), SignedWadZeroable::zero(), "SignedWad zero mul #4");

        let zero = SignedRay { val: 0, sign: false };
        let neg_zero = SignedRay { val: 0, sign: true };
        let one = SignedRay { val: RAY_ONE, sign: false }; // 1.0 ray
        let neg_one = SignedRay { val: RAY_ONE, sign: true }; // -1.0 ray

        assert_eq!((one * zero), SignedRayZeroable::zero(), "SignedRay zero mul #1");
        assert_eq!((neg_one * zero), SignedRayZeroable::zero(), "SignedRay zero mul #2");
        assert_eq!((one * neg_zero), SignedRayZeroable::zero(), "SignedRay zero mul #3");
        assert_eq!((neg_one * neg_zero), SignedRayZeroable::zero(), "SignedRay zero mul #4");
    }

    #[test]
    #[should_panic(expected: 'u256 is 0')]
    fn test_signed_wad_zero_div() {
        let zero = SignedWad { val: 0, sign: false };
        let one = SignedWad { val: WAD_ONE, sign: false };
        let res: SignedWad = one / zero;
    }

    #[test]
    #[should_panic(expected: 'u256 is 0')]
    fn test_signed_wad_neg_zero_div() {
        let neg_zero = SignedWad { val: 0, sign: true };
        let one = SignedWad { val: WAD_ONE, sign: false };
        let res: SignedWad = one / neg_zero;
    }

    #[test]
    #[should_panic(expected: 'u256 is 0')]
    fn test_signed_ray_zero_div() {
        let zero = SignedRay { val: 0, sign: false };
        let one = SignedRay { val: RAY_ONE, sign: false };
        let res: SignedRay = one / zero;
    }

    #[test]
    #[should_panic(expected: 'u256 is 0')]
    fn test_signed_ray_neg_zero_div() {
        let neg_zero = SignedRay { val: 0, sign: true };
        let one = SignedRay { val: RAY_ONE, sign: false };
        let res: SignedRay = one / neg_zero;
    }

    #[test]
    fn test_mul_eq() {
        let mut a1 = SignedWad { val: 5, sign: true };
        let a2 = SignedWad { val: 5, sign: true };
        let b = SignedWad { val: 3, sign: false };

        a1 *= b;
        assert_eq!(a1, a2 * b, "Incorrect MulEq #1");

        let mut a1 = SignedRay { val: 5, sign: true };
        let a2 = SignedRay { val: 5, sign: true };
        let b = SignedRay { val: 3, sign: false };

        a1 *= b;
        assert_eq!(a1, a2 * b, "Incorrect MulEq #2");
    }

    #[test]
    fn test_div_eq() {
        let mut a1 = SignedWad { val: 15, sign: true };
        let a2 = SignedWad { val: 15, sign: true };
        let b = SignedWad { val: 3, sign: false };

        a1 /= b;
        assert_eq!(a1, a2 / b, "Incorrect DivEq #1");

        let mut a1 = SignedRay { val: 15, sign: true };
        let a2 = SignedRay { val: 15, sign: true };
        let b = SignedRay { val: 3, sign: false };

        a1 /= b;
        assert_eq!(a1, a2 / b, "Incorrect DivEq #2");
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
        let one = SignedWad { val: WAD_ONE, sign: false };
        let neg_one = SignedWad { val: WAD_ONE, sign: true };

        assert_eq!(BoundedSignedWad::min(), SignedWad { val: max_u128, sign: true }, "SignedWad min");
        assert_eq!(BoundedSignedWad::max(), SignedWad { val: max_u128, sign: false }, "SignedWad max");

        assert_eq!((BoundedSignedWad::min() * neg_one), BoundedSignedWad::max(), "SignedWad min mul");
        assert_eq!((BoundedSignedWad::max() * neg_one), BoundedSignedWad::min(), "SignedWad max mul");

        let one = SignedRay { val: RAY_ONE, sign: false };
        let neg_one = SignedRay { val: RAY_ONE, sign: true };

        assert_eq!(BoundedSignedRay::min(), SignedRay { val: max_u128, sign: true }, "SignedRay min");
        assert_eq!(BoundedSignedRay::max(), SignedRay { val: max_u128, sign: false }, "SignedRay max");

        assert_eq!((BoundedSignedRay::min() * neg_one), BoundedSignedRay::max(), "SignedRay min mul");
        assert_eq!((BoundedSignedRay::max() * neg_one), BoundedSignedRay::min(), "SignedRay max mul");
    }

    #[test]
    fn test_into_conversions() {
        // Test U128IntoSignedWad
        let a: u128 = 100;
        let a_signed: SignedWad = a.into();
        assert_eq!(a_signed.val, a, "U128IntoSignedWad val fail");
        assert(!a_signed.sign, 'U128IntoSignedWad sign fail');

        // Test WadIntoSignedWad
        let b = Wad { val: 200 };
        let b_signed: SignedWad = b.into();
        assert_eq!(b_signed.val, b.val, "WadIntoSignedWad val fail");
        assert(!b_signed.sign, 'WadIntoSignedWad sign fail');

        // Test SignedWadTryIntoWad
        let d = SignedWad { val: 400, sign: false };
        let d_wad: Option<Wad> = d.try_into();
        assert(d_wad.is_some(), 'SignedWadTryIntoWad pos fail');
        assert_eq!(d_wad.unwrap().val, d.val, "SignedWadTryIntoWad val fail");

        let e = SignedWad { val: 500, sign: true };
        let e_wad: Option<Wad> = e.try_into();
        assert(e_wad.is_none(), 'SignedWadTryIntoWad neg fail');

        // Test U128IntoSignedRay
        let a: u128 = 100;
        let a_signed: SignedRay = a.into();
        assert_eq!(a_signed.val, a, "U128IntoSignedRay val fail");
        assert(!a_signed.sign, 'U128IntoSignedRay sign fail');

        // Test RayIntoSignedRay
        let b = Ray { val: 200 };
        let b_signed: SignedRay = b.into();
        assert_eq!(b_signed.val, b.val, "RayIntoSignedRay val fail");
        assert(!b_signed.sign, 'RayIntoSignedRay sign fail');

        // Test WadIntoSignedRay
        let c = Wad { val: 300 * WAD_ONE };
        let c_signed: SignedRay = c.into();
        assert_eq!(c_signed.val, c.val * DIFF, "WadIntoSignedRay val fail");
        assert(!c_signed.sign, 'WadIntoSignedRay sign fail');

        // Test SignedRayTryIntoRay
        let d = SignedRay { val: 400, sign: false };
        let d_ray: Option<Ray> = d.try_into();
        assert(d_ray.is_some(), 'SignedRayTryIntoRay pos fail');
        assert_eq!(d_ray.unwrap().val, d.val, "SignedRayTryIntoRay val fail");

        let e = SignedRay { val: 500, sign: true };
        let e_ray: Option<Ray> = e.try_into();
        assert(e_ray.is_none(), 'SignedRayTryIntoRay neg fail');
    }

    #[test]
    fn test_zeroable_oneable() {
        // Test SignedWadZeroable
        let zero = SignedWadZeroable::zero();
        assert_eq!(zero.val, 0, "Zeroable zero fail");
        assert(!zero.sign, 'Zeroable zero sign fail');
        assert(zero.is_zero(), 'Zeroable is_zero fail');
        assert(!zero.is_non_zero(), 'Zeroable is_non_zero fail');

        let non_zero = SignedWad { val: 100, sign: false };
        assert(!non_zero.is_zero(), 'Zeroable non_zero fail');
        assert(non_zero.is_non_zero(), 'Zeroable non_zero fail');

        // Test SignedWadOneable
        let one = SignedWadOneable::one();
        assert_eq!(one.val, WAD_ONE, "Oneable one fail");
        assert(!one.sign, 'Oneable one sign fail');
        assert(one.is_one(), 'Oneable is_one fail');
        assert(!one.is_non_one(), 'Oneable is_non_one fail');

        let minus_one = SignedWad { val: WAD_ONE, sign: true };
        assert(!minus_one.is_one(), 'Oneable minus_one is_one fail');
        assert(minus_one.is_non_one(), 'Oneable minus_one is_non_one f');

        let non_one = SignedWad { val: 200, sign: false };
        assert(!non_one.is_one(), 'Oneable non_one fail');
        assert(non_one.is_non_one(), 'Oneable non_one fail');

        // Test SignedRayZeroable
        let zero = SignedRayZeroable::zero();
        assert_eq!(zero.val, 0, "Zeroable zero fail");
        assert(!zero.sign, 'Zeroable zero sign fail');
        assert(zero.is_zero(), 'Zeroable is_zero fail');
        assert(!zero.is_non_zero(), 'Zeroable is_non_zero fail');

        let non_zero = SignedRay { val: 100, sign: false };
        assert(!non_zero.is_zero(), 'Zeroable non_zero fail');
        assert(non_zero.is_non_zero(), 'Zeroable non_zero fail');

        // Test SignedRayOneable
        let one = SignedRayOneable::one();
        assert_eq!(one.val, RAY_ONE, "Oneable one fail");
        assert(!one.sign, 'Oneable one sign fail');
        assert(one.is_one(), 'Oneable is_one fail');
        assert(!one.is_non_one(), 'Oneable is_non_one fail');

        let minus_one = SignedRay { val: RAY_ONE, sign: true };
        assert(!minus_one.is_one(), 'Oneable minus_one is_one fail');
        assert(minus_one.is_non_one(), 'Oneable minus_one is_non_one f');

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

        assert_eq!(pos_zero, neg_zero, "Zero eq");
        assert(!(pos_zero != neg_zero), 'Zero neq');
        assert(pos_zero >= neg_zero, 'Zero ge');
        assert(pos_zero <= neg_zero, 'Zero le');
        assert(!(pos_zero > neg_zero), 'Zero gt');
        assert(!(pos_zero < neg_zero), 'Zero lt');

        let pos_zero = SignedRay { val: 0, sign: false };
        let neg_zero = SignedRay { val: 0, sign: true };

        assert_eq!(pos_zero, neg_zero, "Zero eq");
        assert(!(pos_zero != neg_zero), 'Zero neq');
        assert(pos_zero >= neg_zero, 'Zero ge');
        assert(pos_zero <= neg_zero, 'Zero le');
        assert(!(pos_zero > neg_zero), 'Zero gt');
        assert(!(pos_zero < neg_zero), 'Zero lt');
    }

    #[test]
    fn test_display_and_debug() {
        let w = SignedWad { val: 123, sign: true };
        assert_eq!(format!("{}", w), "-123", "SignedWad display");
        assert_eq!(format!("{:?}", w), "-123", "SignedWad debug");

        let r = SignedRay { val: 456, sign: false };
        assert_eq!(format!("{}", r), "456", "SignedRay display");
        assert_eq!(format!("{:?}", r), "456", "SignedRay debug");
    }
}
