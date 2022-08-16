import os
from collections import namedtuple
from decimal import Decimal
from functools import cache
from typing import Union

from starkware.starknet.compiler.compile import compile_starknet_files
from starkware.starknet.services.api.contract_class import ContractClass

Uint256 = namedtuple("Uint256", "low high")

PRIME = 2**251 + 17 * 2**192 + 1
RANGE_CHECK_BOUND = 2**128

WAD_SCALE = 10**18
RAY_SCALE = 10**27
WAD_RAY_DIFF = RAY_SCALE // WAD_SCALE


def here() -> str:
    return os.path.abspath(os.path.dirname(__file__))


def contract_path(rel_contract_path: str) -> str:
    return os.path.join(here(), "..", rel_contract_path)


@cache
def compile_contract(rel_contract_path: str) -> ContractClass:
    contract_src = contract_path(rel_contract_path)
    tld = os.path.join(here(), "..")
    return compile_starknet_files(
        [contract_src],
        debug_info=True,
        disable_hint_validation=True,
        cairo_path=[tld],
    )


def signed_int_to_felt(a: int) -> int:
    # Takes in integer value, returns input if positive, otherwise return PRIME + input
    if a >= 0:
        return a
    return PRIME + a


def to_ray(n: Union[int, float, Decimal]) -> int:
    # Multiply the input value by RAY_SCALE
    return int(n * RAY_SCALE)


def to_uint(a: int) -> Uint256:
    # Takes in value, returns Uint256 tuple
    return Uint256(low=(a & ((1 << 128) - 1)), high=(a >> 128))


def to_wad(n: Union[int, float, Decimal]) -> int:
    # Multiply the input value by WAD_SCALE
    return int(n * WAD_SCALE)


def wad_to_ray(n: int) -> int:
    # Convert a wad value to a ray value
    return int(n * (RAY_SCALE // WAD_SCALE))
