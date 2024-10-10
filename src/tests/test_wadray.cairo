use core::num::traits::{One, Bounded, Sqrt, Zero};
use wadray::tests::utils::assert_equalish;
use wadray::{
    BoundedRay, BoundedWad, DIFF, MAX_CONVERTIBLE_WAD, Ray, RAY_ONE, ray_to_wad, rdiv_wr, rdiv_ww, rmul_rw, rmul_wr,
    Wad, WAD_ONE, WAD_DECIMALS, WAD_SCALE, wdiv_rw, wmul_rw, wmul_wr,
};

#[test]
fn test_add() {
    // 0 + 0 = 0
    assert_eq!(Wad { val: 0 } + Wad { val: 0 }, Wad { val: 0 }, "Incorrect addition #1");

    // 1 + 1 = 2
    assert_eq!(Wad { val: 1 } + Wad { val: 1 }, Wad { val: 2 }, "Incorrect addition #2");

    // 123456789101112 + 121110987654321 = 244567776755433
    assert_eq!(
        Wad { val: 123456789101112 } + Wad { val: 121110987654321 },
        Wad { val: 244567776755433 },
        "Incorrect addition #3"
    );

    // 0 + 0 = 0
    assert_eq!(Ray { val: 0 } + Ray { val: 0 }, Ray { val: 0 }, "Incorrect addition #4");

    // 1 + 1 = 2
    assert_eq!(Ray { val: 1 } + Ray { val: 1 }, Ray { val: 2 }, "Incorrect addition #5");

    // 123456789101112 + 121110987654321 = 244567776755433
    assert_eq!(
        Ray { val: 123456789101112 } + Ray { val: 121110987654321 },
        Ray { val: 244567776755433 },
        "Incorrect addition #6"
    );
}

#[test]
fn test_add_eq() {
    let mut a1 = Wad { val: 5 };
    let a2 = Wad { val: 5 };
    let b = Wad { val: 3 };

    a1 += b;
    assert_eq!(a1, a2 + b, "Incorrect AddEq #1");

    let mut a1 = Ray { val: 5 };
    let a2 = Ray { val: 5 };
    let b = Ray { val: 3 };

    a1 += b;
    assert_eq!(a1, a2 + b, "Incorrect AddEq #2");
}


#[test]
fn test_sub() {
    // 0 - 0 = 0
    assert_eq!(Wad { val: 0 } - Wad { val: 0 }, Wad { val: 0 }, "Incorrect subtraction #1");

    // 2 - 1 = 1
    assert_eq!(Wad { val: 2 } - Wad { val: 1 }, Wad { val: 1 }, "Incorrect subtraction #2");

    // 244567776755433 - 121110987654321 = 123456789101112
    assert_eq!(
        Wad { val: 244567776755433 } - Wad { val: 121110987654321 },
        Wad { val: 123456789101112 },
        "Incorrect subtraction #3"
    );

    // 0 - 0 = 0
    assert_eq!(Ray { val: 0 } - Ray { val: 0 }, Ray { val: 0 }, "Incorrect subtraction #4");

    // 2 - 1 = 1
    assert_eq!(Ray { val: 2 } - Ray { val: 1 }, Ray { val: 1 }, "Incorrect subtraction #5");

    // 244567776755433 - 121110987654321 = 123456789101112
    assert_eq!(
        Ray { val: 244567776755433 } - Ray { val: 121110987654321 },
        Ray { val: 123456789101112 },
        "Incorrect subtraction #6"
    );
}

#[test]
fn test_sub_eq() {
    let mut a1 = Wad { val: 5 };
    let a2 = Wad { val: 5 };
    let b = Wad { val: 3 };

    a1 -= b;
    assert_eq!(a1, a2 - b, "Incorrect SubEq #1");

    let mut a1 = Ray { val: 5 };
    let a2 = Ray { val: 5 };
    let b = Ray { val: 3 };

    a1 -= b;
    assert_eq!(a1, a2 - b, "Incorrect SubEq #2");
}


#[test]
fn test_mul() {
    // 0 * 69 = 0
    assert_eq!(Wad { val: 0 } * Wad { val: 69 }, Wad { val: 0 }, "Incorrect Multiplication # 1");

    // 1 * 1 = 0 (truncated)
    assert_eq!(
        Wad { val: 1 } * Wad { val: 1 }, Wad { val: 0 }, "Incorrect multiplication #2"
    ); // Result should be truncated

    // 1 (wad) * 1 (wad) = 1 (wad)
    assert_eq!(Wad { val: WAD_ONE } * Wad { val: WAD_ONE }, Wad { val: WAD_ONE }, "Incorrect multiplication #3");

    // 121110987654321531059 * 1234567891011125475893 = 149519736606670187008926
    assert_eq!(
        Wad { val: 121110987654321531059 } * Wad { val: 1234567891011125475893 },
        Wad { val: 149519736606670187008926 },
        "Incorrect multiplication #4"
    );

    // 0 * 69 = 0
    assert_eq!(Ray { val: 0 } * Ray { val: 69 }, Ray { val: 0 }, "Incorrect Multiplication #5");

    // 1 * 1 = 0 (truncated)
    assert_eq!(
        Ray { val: 1 } * Ray { val: 1 }, Ray { val: 0 }, "Incorrect multiplication #6"
    ); // Result should be truncated

    // 1 (ray) * 1 (ray) = 1 (ray)
    assert_eq!(Ray { val: RAY_ONE } * Ray { val: RAY_ONE }, Ray { val: RAY_ONE }, "Incorrect multiplication #7");

    // 121110987654321531059 * 1234567891011125475893 = 149519736606670 (truncated)
    assert_eq!(
        Ray { val: 121110987654321531059 } * Ray { val: 1234567891011125475893 },
        Ray { val: 149519736606670 },
        "Incorrect multiplication #8"
    );

    // wmul(ray, wad) -> ray
    assert_eq!(
        wmul_rw(Ray { val: RAY_ONE }, Wad { val: WAD_ONE }), Ray { val: RAY_ONE }, "Incorrect multiplication #9"
    );

    // wmul(wad, ray) -> ray
    assert_eq!(
        wmul_wr(Wad { val: WAD_ONE }, Ray { val: RAY_ONE }), Ray { val: RAY_ONE }, "Incorrect multiplication #10"
    );

    // rmul(ray, wad) -> wad
    assert_eq!(
        rmul_rw(Ray { val: RAY_ONE }, Wad { val: WAD_ONE }), Wad { val: WAD_ONE }, "Incorrect multiplication #11"
    );

    // rmul(wad, ray) -> wad
    assert_eq!(
        rmul_wr(Wad { val: WAD_ONE }, Ray { val: RAY_ONE }), Wad { val: WAD_ONE }, "Incorrect multiplication #12"
    );
}

#[test]
fn test_mul_eq() {
    let mut a1 = Wad { val: 5 };
    let a2 = Wad { val: 5 };
    let b = Wad { val: 3 };

    a1 *= b;
    assert_eq!(a1, a2 * b, "Incorrect MulEq #1");

    let mut a1 = Ray { val: 5 };
    let a2 = Ray { val: 5 };
    let b = Ray { val: 3 };

    a1 *= b;
    assert_eq!(a1, a2 * b, "Incorrect MulEq #2");
}


#[test]
fn test_div() {
    // 2 / (1 / 2) = 4 (wad)
    assert_eq!(Wad { val: 2 * WAD_ONE } / Wad { val: WAD_ONE / 2 }, Wad { val: 4 * WAD_ONE }, "Incorrect division #1");

    // 2 / (1 / 2) = 4 (ray)
    assert_eq!(Ray { val: 2 * RAY_ONE } / Ray { val: RAY_ONE / 2 }, Ray { val: 4 * RAY_ONE }, "Incorrect division #2");

    // wdiv(ray, wad) -> ray
    assert_eq!(wdiv_rw(Ray { val: RAY_ONE }, Wad { val: WAD_ONE }), Ray { val: RAY_ONE }, "Incorrect division #3");

    // rdiv(wad, ray) -> wad
    assert_eq!(rdiv_wr(Wad { val: WAD_ONE }, Ray { val: RAY_ONE }), Wad { val: WAD_ONE }, "Incorrect division #4");
}

#[test]
fn test_div_eq() {
    let mut a1 = Wad { val: 15 };
    let a2 = Wad { val: 15 };
    let b = Wad { val: 3 };

    a1 /= b;
    assert_eq!(a1, a2 / b, "Incorrect DivEq #1");

    let mut a1 = Ray { val: 15 };
    let a2 = Ray { val: 15 };
    let b = Ray { val: 3 };

    a1 /= b;
    assert_eq!(a1, a2 / b, "Incorrect DivEq #2");
}

#[test]
fn test_div_of_0() {
    let w = Wad { val: 42 };
    let r = Ray { val: 42 };
    let w0 = Wad { val: 0 };
    let r0 = Ray { val: 0 };

    assert_eq!(w0 / w, w0, "w0 / w");
    assert_eq!(r0 / r, r0, "r0 / r");
    assert_eq!(wdiv_rw(r0, w), r0, "wdiv_rw");
    assert_eq!(rdiv_wr(w0, r), w0, "rdiv_wr");
    assert_eq!(rdiv_ww(w0, w), r0, "rdiv_ww");
}

#[test]
#[should_panic(expected: ('Division by 0',))]
fn test_div_wad_fail() {
    let _: Wad = Wad { val: WAD_ONE } / Wad { val: 0 };
}

#[test]
#[should_panic(expected: ('Division by 0',))]
fn test_div_ray_fail() {
    let _: Ray = Ray { val: RAY_ONE } / Ray { val: 0 };
}

#[test]
fn test_conversions() {
    // Test conversion from Wad to Ray
    let a: Ray = Wad { val: WAD_ONE }.try_into().unwrap();
    assert_eq!(a.val, RAY_ONE, "Incorrect wad->ray conversion");

    let a: Ray = Wad { val: MAX_CONVERTIBLE_WAD }.try_into().unwrap();
    assert_eq!(a.val, MAX_CONVERTIBLE_WAD * DIFF, "Incorrect wad->ray conversion");

    let a: Option::<Ray> = Wad { val: MAX_CONVERTIBLE_WAD + 1 }.try_into();
    assert(a.is_none(), 'Incorrect wad->ray conversion');

    // Test conversion from Ray to Wad
    let a: Ray = Ray { val: RAY_ONE };
    assert_eq!(ray_to_wad(a).val, WAD_ONE, "Incorrect ray->wad conversion");
}

#[test]
fn test_conversions_from_primitive_types() {
    assert_eq!(Wad { val: 1 }, 1_u8.into(), "Wad u8");
    assert_eq!(Wad { val: 1 }, 1_u16.into(), "Wad u16");
    assert_eq!(Wad { val: 1 }, 1_u32.into(), "Wad u32");
    assert_eq!(Wad { val: 1 }, 1_u64.into(), "Wad u64");
    assert_eq!(Wad { val: 1 }, 1_u128.into(), "Wad u128");

    assert_eq!(Ray { val: 1 }, 1_u8.into(), "Ray u8");
    assert_eq!(Ray { val: 1 }, 1_u16.into(), "Ray u16");
    assert_eq!(Ray { val: 1 }, 1_u32.into(), "Ray u32");
    assert_eq!(Ray { val: 1 }, 1_u64.into(), "Ray u64");
    assert_eq!(Ray { val: 1 }, 1_u128.into(), "Ray u128");
}

#[test]
fn test_bounded() {
    let max_u128 = 0xffffffffffffffffffffffffffffffff;

    assert_eq!(BoundedWad::MIN, Wad { val: 0 }, "Wad min");
    assert_eq!(BoundedWad::MAX, Wad { val: max_u128 }, "Wad max");

    assert_eq!(BoundedRay::MIN, Ray { val: 0 }, "Ray min");
    assert_eq!(BoundedRay::MAX, Ray { val: max_u128 }, "Ray max");
}

#[test]
fn test_wadray_into_u256() {
    // Test WadIntoU256
    assert_eq!(Wad { val: 5 }.into(), 5_u256, "Incorrect Wad->u256 conversion")
}

#[test]
fn test_u256_try_into_wadray() {
    // Test U256TryIntoWad
    assert_eq!(Wad { val: 5 }, 5_u256.try_into().unwrap(), "Incorrect u256->Wad conversion");
}

#[test]
#[should_panic(expected: ('Option::unwrap failed.',))]
fn test_conversions_fail2() {
    let _: Ray = Wad { val: MAX_CONVERTIBLE_WAD + 1 }.try_into().unwrap();
}

// comparison tests are split into 2 fns to overcome a test runner bug
#[test]
fn test_comparisons1() {
    // Test Wad type comparison operators: <, >, <=, >=
    assert(Wad { val: WAD_ONE } < Wad { val: WAD_ONE + 1 }, 'Incorrect < comparison #1');
    assert(Wad { val: WAD_ONE + 1 } > Wad { val: WAD_ONE }, 'Incorrect > comparison #2');
    assert(Wad { val: WAD_ONE } <= Wad { val: WAD_ONE }, 'Incorrect <= comparison #3');
    assert(Wad { val: WAD_ONE + 1 } >= Wad { val: WAD_ONE + 1 }, 'Incorrect >= comparison #4');

    // Test Ray type comparison operators: <, >, <=, >=
    assert(Ray { val: RAY_ONE } < Ray { val: RAY_ONE + 1 }, 'Incorrect < comparison #5');
    assert(Ray { val: RAY_ONE + 1 } > Ray { val: RAY_ONE }, 'Incorrect > comparison #6');
    assert(Ray { val: RAY_ONE } <= Ray { val: RAY_ONE }, 'Incorrect <= comparison #7');
    assert(Ray { val: RAY_ONE + 1 } >= Ray { val: RAY_ONE + 1 }, 'Incorrect >= comparison #8');

    // Test Ray type opposite comparisons: !(<), !(>), !(<=), !(>=)
    assert(!(Ray { val: RAY_ONE } < Ray { val: RAY_ONE }), 'Incorrect < comparison #9');
    assert(!(Ray { val: RAY_ONE } > Ray { val: RAY_ONE }), 'Incorrect > comparison #10');
    assert(!(Ray { val: RAY_ONE + 1 } <= Ray { val: RAY_ONE }), 'Incorrect <= comparison #11');
    assert(!(Ray { val: RAY_ONE } >= Ray { val: RAY_ONE + 1 }), 'Incorrect >= comparison #12');

    // Test Wad type opposite comparisons: !(<), !(>), !(<=), !(>=)
    assert(!(Wad { val: WAD_ONE } < Wad { val: WAD_ONE }), 'Incorrect < comparison #13');
    assert(!(Wad { val: WAD_ONE } > Wad { val: WAD_ONE }), 'Incorrect > comparison #14');
    assert(!(Wad { val: WAD_ONE + 1 } <= Wad { val: WAD_ONE }), 'Incorrect <= comparison #15');
    assert(!(Wad { val: WAD_ONE } >= Wad { val: WAD_ONE + 1 }), 'Incorrect >= comparison #16');
}

#[test]
fn test_comparisons2() {
    // Test Wad type != operator
    assert(Wad { val: WAD_ONE } != Wad { val: WAD_ONE + 1 }, 'Incorrect != comparison #17');
    assert(!(Wad { val: WAD_ONE } != Wad { val: WAD_ONE }), 'Incorrect != comparison #18');

    // Test Ray type != operator
    assert(Ray { val: RAY_ONE } != Ray { val: RAY_ONE + 1 }, 'Incorrect != comparison #19');
    assert(!(Ray { val: RAY_ONE } != Ray { val: RAY_ONE }), 'Incorrect != comparison #20');
}

#[test]
fn test_zero() {
    // Test zero
    let wad_zero: Wad = Zero::zero();
    assert_eq!(wad_zero.val, 0, "Value should be 0 #1");

    // Test is_zero
    let wad_one = Wad { val: 1 };
    assert(wad_zero.is_zero(), 'Value should be 0 #2');
    assert(!wad_one.is_zero(), 'Value should not be 0 #3');

    // Test is_non_zero
    assert(!wad_zero.is_non_zero(), 'Value should be 0 #4');
    assert(wad_one.is_non_zero(), 'Value should not be 0 #5');

    // Test zero
    let ray_zero: Ray = Zero::zero();
    assert_eq!(ray_zero.val, 0, "Value should be 0 #6");

    // Test is_zero
    let ray_one = Ray { val: 1 };
    assert(ray_zero.is_zero(), 'Value should be 0 #7');
    assert(!ray_one.is_zero(), 'Value should not be 0 #8');

    // Test is_non_zero
    assert(!ray_zero.is_non_zero(), 'Value should be 0 #9');
    assert(ray_one.is_non_zero(), 'Value should not be 0 #10');
}

#[test]
fn test_one() {
    // Test one
    let wad_one: Wad = One::one();
    assert_eq!(wad_one.val, 1000000000000000000, "Value should be WAD_ONE #1");

    // Test is_one
    let wad_zero: Wad = Zero::zero();
    assert(wad_one.is_one(), 'Value should be 1 #2');
    assert(!wad_zero.is_one(), 'Value should not be 1 #3');

    // Test is_non_one
    assert(!wad_one.is_non_one(), 'Value should be 1 #4');
    assert(wad_zero.is_non_one(), 'Value should not be 1 #5');

    // Test one
    let ray_one: Ray = One::one();
    assert_eq!(ray_one.val, 1000000000000000000000000000, "Value should be RAY_ONE #6");

    // Test is_one
    let ray_zero: Ray = Zero::zero();
    assert(ray_one.is_one(), 'Value should be 1 #7');
    assert(!ray_zero.is_one(), 'Value should not be 1 #8');

    // Test is_non_one
    assert(!ray_one.is_non_one(), 'Value should be 1 #9');
    assert(ray_zero.is_non_one(), 'Value should not be 1 #10');
}

#[test]
fn test_sqrt() {
    let ERROR_MARGIN: Ray = 1_u128.into();

    let val: Ray = Zero::zero();
    let sqrt: Ray = Sqrt::sqrt(val);
    assert(sqrt.val == Zero::zero(), 'wrong sqrt #1');

    // Ground truth tests

    // 1000
    let val: Ray = 1000000000000000000000000000000_u128.into();
    assert_equalish(Sqrt::sqrt(val), 31622776601683793319988935444_u128.into(), ERROR_MARGIN, 'wrong sqrt #2');

    // 6969
    let val: Ray = 6969000000000000000000000000000_u128.into();
    assert_equalish(Sqrt::sqrt(val), 83480536653761396384637711221_u128.into(), ERROR_MARGIN, 'wrong sqrt #3');

    // pi
    let val: Ray = 3141592653589793238462643383_u128.into();
    assert_equalish(Sqrt::sqrt(val), 1772453850905516027298167483_u128.into(), ERROR_MARGIN, 'wrong sqrt #4');

    // e
    let val: Ray = 2718281828459045235360287471_u128.into();
    assert_equalish(Sqrt::sqrt(val), 1648721270700128146848650787_u128.into(), ERROR_MARGIN, 'wrong sqrt #5');

    // Testing the property x = sqrt(x)^2

    let ERROR_MARGIN: Ray = 1000_u128.into();

    let val: Ray = (4 * RAY_ONE).into();
    let sqrt: Ray = Sqrt::sqrt(val);
    assert_equalish((4 * RAY_ONE).into(), sqrt * sqrt, ERROR_MARGIN, 'wrong sqrt #6');

    let val: Ray = (1000 * RAY_ONE).into();
    let sqrt: Ray = Sqrt::sqrt(val);
    assert_equalish((1000 * RAY_ONE).into(), sqrt * sqrt, ERROR_MARGIN, 'wrong sqrt #7');

    // tau
    let val: Ray = 6283185307179586476925286766_u128.into();
    let sqrt: Ray = Sqrt::sqrt(val);
    assert_equalish(6283185307179586476925286766_u128.into(), sqrt * sqrt, ERROR_MARGIN, 'wrong sqrt #8');

    // testing the maximum possible value `sqrt` could accept doesn't cause it to fail
    let val: Ray = Bounded::MAX;
    Sqrt::sqrt(val);
}

#[test]
fn test_display_and_debug() {
    let w = Wad { val: 123 };
    assert_eq!(format!("{}", w), "123", "Wad display");
    assert_eq!(format!("{:?}", w), "123", "Wad debug");

    let r = Ray { val: 456 };
    assert_eq!(format!("{}", r), "456", "Ray display");
    assert_eq!(format!("{:?}", r), "456", "Ray debug");
}

#[test]
fn test_default() {
    let w: Wad = Default::default();
    assert_eq!(w.val, 0, "Wad default");

    let r: Ray = Default::default();
    assert_eq!(r.val, 0, "Ray default");
}
