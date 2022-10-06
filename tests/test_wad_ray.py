import asyncio
import math
import operator

import pytest
from hypothesis import assume, example, given, settings
from hypothesis import strategies as st
from starkware.starknet.testing.contract import StarknetContract
from starkware.starknet.testing.starknet import Starknet
from starkware.starkware_utils.error_handling import StarkException

from tests.utils import (
    PRIME,
    RANGE_CHECK_BOUND,
    RAY_SCALE,
    WAD_RAY_DIFF,
    WAD_SCALE,
    compile_contract,
    signed_int_to_felt,
    to_ray,
    to_uint,
    to_wad,
    wad_to_ray,
)

BOUND = 2**125


st_int = st.integers(min_value=-(2**250), max_value=2**250)
st_int125 = st.integers(min_value=-(2**125), max_value=2**125)
st_uint125 = st.integers(min_value=1, max_value=2**125)
st_uint = st.integers(min_value=0, max_value=2 * 200)


@pytest.fixture(scope="session")
def event_loop():
    return asyncio.new_event_loop()


@pytest.fixture(scope="session")
async def starknet_session() -> Starknet:
    starknet = await Starknet.empty()
    return starknet


@pytest.fixture(scope="session")
async def wad_ray(starknet_session: Starknet) -> StarknetContract:
    contract = compile_contract("tests/test_wad_ray.cairo")
    wad_ray = await starknet_session.deploy(contract_class=contract, constructor_calldata=[])
    return wad_ray


BOUND_TEST_CASES = [-(BOUND + 1), -BOUND, -1, 0, 1, BOUND - 1, BOUND, BOUND + 1]


@pytest.mark.parametrize("val", BOUND_TEST_CASES)
@pytest.mark.asyncio
async def test_assert_valid(wad_ray, val):
    if abs(val) > BOUND:
        with pytest.raises(StarkException):
            await wad_ray.test_assert_valid(val).execute()
    else:
        await wad_ray.test_assert_valid(val).execute()


@pytest.mark.parametrize("val", BOUND_TEST_CASES)
@pytest.mark.asyncio
async def test_assert_valid_unsigned(wad_ray, val):
    if val < 0 or val > BOUND:
        with pytest.raises(StarkException):
            await wad_ray.test_assert_valid_unsigned(val).execute()
    else:
        await wad_ray.test_assert_valid_unsigned(val).execute()


@settings(max_examples=50, deadline=None)
@given(val=st_int)
@example(val=to_wad(RANGE_CHECK_BOUND) + 1)
@example(val=to_wad(RANGE_CHECK_BOUND))
@example(val=to_wad(BOUND + 1))
@example(val=to_wad(BOUND))
@example(val=to_wad(to_wad(25)))  # Test exact multiple of wad - should return same value
@example(val=0)
@example(val=-to_wad(BOUND + 1))
@example(val=-to_wad(BOUND))
@example(val=to_wad(-RANGE_CHECK_BOUND))
@example(val=to_wad(-(RANGE_CHECK_BOUND + 1)))
@pytest.mark.asyncio
async def test_floor(wad_ray, val):
    # For positive integers, input value to contract call is same as value
    input_val = signed_int_to_felt(val)

    # Perform integer division
    q = val // WAD_SCALE
    expected_py = to_wad(math.floor(q))
    expected_cairo = signed_int_to_felt(expected_py)

    if q < (-BOUND) or q >= BOUND:
        # Exception raised by Cairo's builtin `signed_div_rem`
        # -bound <= q < bound
        with pytest.raises(StarkException):
            await wad_ray.test_floor(input_val).execute()
    elif abs(expected_py) > BOUND:
        with pytest.raises(StarkException, match="WadRay: out of bounds"):
            await wad_ray.test_floor(input_val).execute()
    else:
        res = (await wad_ray.test_floor(input_val).execute()).result.res
        assert res == expected_cairo


@settings(max_examples=50, deadline=None)
@given(val=st_int)
@example(val=to_wad(RANGE_CHECK_BOUND) + 1)
@example(val=to_wad(RANGE_CHECK_BOUND))
@example(val=to_wad(BOUND + 1))
@example(val=to_wad(BOUND))
@example(val=to_wad(to_wad(25)))  # Test exact multiple of wad - should return same value
@example(val=0)
@example(val=-to_wad(BOUND + 1))
@example(val=-to_wad(BOUND))
@example(val=to_wad(-RANGE_CHECK_BOUND))
@example(val=to_wad(-(RANGE_CHECK_BOUND + 1)))
@pytest.mark.asyncio
async def test_ceil(wad_ray, val):
    # For positive integers, input value to contract call is same as value
    input_val = signed_int_to_felt(val)

    # Perform integer division
    q = val // WAD_SCALE
    r = val % WAD_SCALE
    expected_py = to_wad(math.floor(q))

    if r == 0:
        # If exact multiple of wad (i.e. no remainder), input value should be returned.
        expected_cairo = val
    else:
        # Otherwise, round up by adding one wad
        expected_cairo = signed_int_to_felt(expected_py + WAD_SCALE)

    if q < (-BOUND) or q >= BOUND:
        # Exception raised by Cairo's builtin `signed_div_rem`
        # -bound <= q < bound
        with pytest.raises(StarkException):
            await wad_ray.test_ceil(input_val).execute()
    elif abs(expected_py) > BOUND:
        with pytest.raises(StarkException, match="WadRay: out of bounds"):
            await wad_ray.test_ceil(input_val).execute()
    else:
        res = (await wad_ray.test_ceil(input_val).execute()).result.res
        assert res == expected_cairo


@settings(max_examples=50, deadline=None)
@given(left=st_int125, right=st_int125)
@example(left=0, right=-1)
@example(left=-1, right=0)
@example(left=0, right=1)
@example(left=0, right=0)
@example(left=1, right=0)
@example(left=to_wad(1), right=to_wad(1))  # Test wad values
@pytest.mark.parametrize("fn,op", [("test_add", operator.add), ("test_sub", operator.sub)])
@pytest.mark.asyncio
async def test_add_sub(wad_ray, left, right, fn, op):
    left_input_val = signed_int_to_felt(left)
    right_input_val = signed_int_to_felt(right)

    expected_py = op(left, right)
    expected_cairo = signed_int_to_felt(expected_py)
    method = wad_ray.get_contract_function(fn)

    if abs(expected_py) > BOUND:
        with pytest.raises(StarkException, match="WadRay: out of bounds"):
            await method(left_input_val, right_input_val).execute()

    else:
        res = (await method(left_input_val, right_input_val).execute()).result.res
        assert res == expected_cairo


@settings(max_examples=50, deadline=None)
@given(left=st_uint125, right=st_uint125)
@example(left=0, right=1)
@example(left=0, right=0)
@example(left=1, right=0)
@example(left=to_wad(1), right=to_wad(1))  # Test wad values
@pytest.mark.parametrize("fn,op", [("test_add_unsigned", operator.add), ("test_sub_unsigned", operator.sub)])
@pytest.mark.asyncio
async def test_add_sub_unsigned(wad_ray, left, right, fn, op):
    expected_py = op(left, right)
    expected_cairo = signed_int_to_felt(expected_py)
    method = wad_ray.get_contract_function(fn)

    if expected_py < 0 or expected_py > BOUND:
        with pytest.raises(StarkException, match="WadRay: out of bounds"):
            await method(left, right).execute()

    else:
        res = (await method(left, right).execute()).result.res
        assert res == expected_cairo


@settings(max_examples=50, deadline=None)
@given(left=st_int125, right=st_int125)
@example(left=to_wad(1), right=to_wad(1))  # Test wad values
@example(left=to_wad(2), right=to_wad(2))  # Test wad values
@example(left=to_wad(1), right=to_wad(1) // 2)  # Test percentage
@example(left=to_ray(1), right=to_ray(1))  # Test wad values
@example(left=to_ray(2), right=to_ray(2))  # Test wad values
@example(left=to_ray(1), right=to_ray(1) // 2)  # Test percentage
@pytest.mark.parametrize(
    "fn,op,scale,ret",
    [
        ("test_wmul", operator.mul, WAD_SCALE, "res"),
        ("test_wsigned_div", operator.floordiv, WAD_SCALE, "res"),
        ("test_rmul", operator.mul, RAY_SCALE, "res"),
        ("test_rsigned_div", operator.floordiv, RAY_SCALE, "res"),
    ],
)
@pytest.mark.asyncio
async def test_mul_div_signed(wad_ray, left, right, fn, op, scale, ret):
    # skip right = 0
    assume(right != 0)

    left_input_val = signed_int_to_felt(left)
    right_input_val = signed_int_to_felt(right)

    if "div" in fn:
        sign = -1 if right < 0 else 1
        # Convert right to absolute value before converting it to felt
        right = abs(right)
        # `signed_div_rem` assumes 0 < right <= PRIME / RANGE_CHECK_BOUND
        assume(right <= PRIME // RANGE_CHECK_BOUND)
        # Scale left by wad after converting it to felt for computation of python value
        left *= scale

    expected_py = op(left, right)

    if "mul" in fn:
        expected_py //= scale

    if "div" in fn:
        expected_py *= sign

    expected_cairo = signed_int_to_felt(expected_py)

    method = wad_ray.get_contract_function(fn)

    if abs(expected_py) > BOUND:
        with pytest.raises(StarkException):
            await method(left_input_val, right_input_val).execute()

    else:
        res = getattr((await method(left_input_val, right_input_val).execute()).result, ret)
        assert res == expected_cairo


@settings(max_examples=50, deadline=None)
@given(left=st_uint125, right=st_uint125)
@example(left=to_wad(1), right=to_wad(1))  # Test wad values
@example(left=to_wad(2), right=to_wad(2))  # Test wad values
@example(left=to_wad(1), right=to_wad(1) // 2)  # Test percentage
@example(left=to_ray(1), right=to_ray(1))  # Test wad values
@example(left=to_ray(2), right=to_ray(2))  # Test wad values
@example(left=to_ray(1), right=to_ray(1) // 2)  # Test percentage
@pytest.mark.parametrize(
    "fn,op,scale,ret",
    [
        ("test_wunsigned_div", operator.floordiv, WAD_SCALE, "res"),
        ("test_wunsigned_div_unchecked", operator.floordiv, WAD_SCALE, "res"),
        ("test_runsigned_div", operator.floordiv, RAY_SCALE, "res"),
        ("test_runsigned_div_unchecked", operator.floordiv, RAY_SCALE, "res"),
    ],
)
@pytest.mark.asyncio
async def test_div_unsigned(wad_ray, left, right, fn, op, scale, ret):
    # `unsigned_div_rem` assumes 0 < right <= PRIME / RANGE_CHECK_BOUND
    assume(right <= PRIME // RANGE_CHECK_BOUND)
    scaled_left = left * scale
    # Exclude values greater than felt after scaling
    assume(scaled_left <= PRIME)
    expected_py = op(scaled_left, right)
    expected_cairo = signed_int_to_felt(expected_py)
    method = wad_ray.get_contract_function(fn)

    if not fn.endswith("unchecked") and abs(expected_py) > BOUND:
        # `unsigned_div_rem` asserts 0 <= quotient < rc_bound, meaning this exception
        # will only catch BOUND < quotient <= rc_bound
        if expected_py < RANGE_CHECK_BOUND:
            with pytest.raises(StarkException, match="WadRay: out of bounds"):
                await method(left, right).execute()
        else:
            with pytest.raises(StarkException):
                await method(left, right).execute()
    elif fn.endswith("unchecked") and expected_py > RANGE_CHECK_BOUND:
        # `unsigned_div_rem` asserts 0 <= quotient < rc_bound,
        with pytest.raises(StarkException):
            await method(left, right).execute()
    else:
        res = getattr((await method(left, right).execute()).result, ret)
        assert res == expected_cairo


@settings(max_examples=50, deadline=None)
@given(val=st_uint125)
@example(val=(BOUND // WAD_RAY_DIFF) + 1)  # Failing case for wad_to_ray
@example(val=(RANGE_CHECK_BOUND // WAD_RAY_DIFF) + 1)  # Failing case for wad_to_ray
@example(val=to_wad((BOUND // WAD_SCALE) + 1))  # Failing case for to_wad
@example(val=to_wad((RANGE_CHECK_BOUND // WAD_SCALE) + 1))  # Failing case for to_wad
@pytest.mark.parametrize(
    "fn,input_op,output_op,ret",
    [
        ("test_to_wad", int, to_wad, "res"),
        ("test_wad_to_felt", to_wad, int, "res"),
        ("test_wad_to_ray", int, wad_to_ray, "res"),
        ("test_wad_to_ray_unchecked", int, wad_to_ray, "res"),
    ],
)
@pytest.mark.asyncio
async def test_wadray_conversions_pass(wad_ray, val, fn, input_op, output_op, ret):
    input_val = input_op(val)
    expected_py = output_op(val)

    method = wad_ray.get_contract_function(fn)

    if fn in ("test_to_wad", "test_wad_to_ray") and abs(expected_py) > BOUND:
        # Test `assert_valid`
        with pytest.raises(StarkException, match="WadRay: out of bounds"):
            await method(input_val).execute()
    elif fn == "test_wad_to_felt" and not (-BOUND <= expected_py < BOUND):
        # Exception for `signed_div_rem`
        with pytest.raises(StarkException):
            await method(input_val).execute()
    else:
        res = getattr((await method(input_val).execute()).result, ret)
        assert res == expected_py


@settings(max_examples=50, deadline=None)
@given(val=st_uint125)
@pytest.mark.parametrize(
    "fn,input_op,output_op,ret", [("test_to_uint", int, to_uint, "uint"), ("test_from_uint", to_uint, int, "res")]
)
@pytest.mark.asyncio
async def test_uint_conversion_pass(wad_ray, val, fn, input_op, output_op, ret):
    input_val = input_op(val)
    expected_py = output_op(val)

    method = wad_ray.get_contract_function(fn)

    res = getattr((await method(input_val).execute()).result, ret)
    assert res == expected_py


@pytest.mark.parametrize("val", [BOUND + 1, RANGE_CHECK_BOUND - 1])
@pytest.mark.asyncio
async def test_from_uint_fail(wad_ray, val):
    val = to_uint(val)
    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await wad_ray.test_from_uint(val).execute()


@pytest.mark.parametrize("func", ["add_unsigned", "sub_unsigned", "wunsigned_div", "runsigned_div"])
@pytest.mark.asyncio
async def test_out_of_bounds_unsigned(wad_ray, func):
    test_func = getattr(wad_ray, "test_" + func)

    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await test_func(2**125 + 1, 0).execute()

    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await test_func(-1, 0).execute()

    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await test_func(0, 2**125 + 1).execute()

    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await test_func(0, -1).execute()


@pytest.mark.parametrize("func", ["add", "sub", "wsigned_div", "rsigned_div"])
@pytest.mark.asyncio
async def test_out_of_bounds_signed(wad_ray, func):
    test_func = getattr(wad_ray, "test_" + func)

    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await test_func(2**125 + 1, 0).execute()

    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await test_func(-(2**125) - 1, 0).execute()

    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await test_func(0, 2**125 + 1).execute()

    with pytest.raises(StarkException, match="WadRay: out of bounds"):
        await test_func(0, -(2**125) - 1).execute()
