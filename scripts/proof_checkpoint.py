"""Describe a requested obligation and the consumer checked by a proof slice.

This metadata supplies Lean types, not a new source of proof evidence. The
slice must check and audit the generated consumer application before reporting
its status. A successful prerequisite check does not close the target.
"""

import json
import re
from argparse import ArgumentTypeError
from dataclasses import dataclass
from pathlib import Path
from typing import Literal

from scripts import field_census as census

WITNESS = "VsaProofSliceCheckpoint.checkedConsumer"


def exact_type(value: str) -> str:
    """Accept a single explicit type expression without holes or commands.

    >>> exact_type("∀ n : Nat, n = n")
    '∀ n : Nat, n = n'
    """
    # Keep quoted literals intact while checking the surrounding Lean syntax.
    code = re.sub(r'"(?:\\.|[^"\\])*"', '""', value)
    if (
        len(value.splitlines()) != 1
        or any(char in value for char in "\r\n\v\f\x1c\x1d\x1e\x85\u2028\u2029")
        or any(token in code for token in ("?", ":=", "#", ";", "--", "/-", "-/", "`"))
        or re.search(r"\b(?:_|by|sorry|admit|axiom|native_decide|bv_decide)\b", code)
        or '"' in code.replace('""', "")
    ):
        raise ValueError(
            "checkpoint types must be single-line explicit expressions without holes or commands"
        )
    stack = []
    pairs = {"(": ")", "[": "]", "{": "}"}
    for char in code:
        if char in pairs:
            stack.append(pairs[char])
        elif char in pairs.values() and (not stack or stack.pop() != char):
            raise ValueError("unbalanced checkpoint type")
    if stack:
        raise ValueError("unbalanced checkpoint type")
    return value


@dataclass(frozen=True)
class Premise:
    """Name an outstanding premise at its exact Lean type."""

    name: str
    type: str


@dataclass(frozen=True)
class Checkpoint:
    """Bind a progress claim to an explicit consumer type check."""

    target_obligation: str
    target_type: str
    consumer: str
    role: Literal["prerequisite", "target"]
    consumer_type: str | None
    remaining_premises: tuple[Premise, ...]

    @property
    def status(self) -> str:
        """Classify only after the caller has checked the consumer."""
        if self.role == "prerequisite":
            return "prerequisite"
        return "conditional" if self.remaining_premises else "complete"

    @property
    def checked_type(self) -> str:
        """Include all remaining premises in a conditional target check."""
        if self.role == "prerequisite":
            assert self.consumer_type is not None
            return self.consumer_type
        binders = "".join(
            f"({item.name} : ({item.type})) → " for item in self.remaining_premises
        )
        return binders + f"({self.target_type})"

    def source(self) -> str:
        """Check the consumer at the acceptance type and audit that application."""
        return (
            f"\nset_option autoImplicit false in\n"
            f"def {WITNESS} : ({self.checked_type}) :=\n  {self.consumer}\n"
            f"#print axioms {WITNESS}\n"
        )


def read_checkpoint(path: Path) -> Checkpoint:
    """Parse a complete checkpoint description before any compiler invocation."""
    raw = json.loads(path.read_text())
    keys = {
        "target_obligation",
        "target_type",
        "consumer",
        "role",
        "remaining_premises",
    }
    if isinstance(raw, dict) and raw.get("role") == "prerequisite":
        keys.add("consumer_type")
    if not isinstance(raw, dict) or set(raw) != keys:
        raise ValueError(f"checkpoint requires exactly these keys: {sorted(keys)}")

    def text(key: str) -> str:
        value = raw[key]
        if not isinstance(value, str) or not value.strip():
            raise ValueError(f"checkpoint {key} must be a nonempty string")
        return value.strip()

    raw_role = text("role")
    role: Literal["prerequisite", "target"]
    if raw_role == "prerequisite":
        role = "prerequisite"
    elif raw_role == "target":
        role = "target"
    else:
        raise ValueError("checkpoint role must be prerequisite or target")
    try:
        consumer = census.lean_identifier(text("consumer"))
    except ArgumentTypeError as error:
        raise ValueError(
            "checkpoint consumer must be a qualified identifier"
        ) from error
    if consumer == WITNESS:
        raise ValueError("checkpoint consumer cannot be its own check")
    premises = raw["remaining_premises"]
    if not isinstance(premises, list):
        raise ValueError("remaining_premises must be an explicit list")
    parsed = []
    for item in premises:
        if not isinstance(item, dict) or set(item) != {"name", "type"}:
            raise ValueError("each remaining premise needs name and type")
        name, type_ = item["name"], item["type"]
        if not isinstance(name, str) or not name.isidentifier():
            raise ValueError("premise name must be an unqualified identifier")
        if not isinstance(type_, str) or not type_.strip():
            raise ValueError("premise type must be a nonempty string")
        parsed.append(Premise(name, exact_type(type_.strip())))
    if len({item.name for item in parsed}) != len(parsed):
        raise ValueError("duplicate remaining premise name")
    target_type = exact_type(text("target_type"))
    consumer_type = (
        exact_type(text("consumer_type")) if role == "prerequisite" else None
    )
    return Checkpoint(
        text("target_obligation"),
        target_type,
        consumer,
        role,
        consumer_type,
        tuple(parsed),
    )
