"""Duplicate-specific validation, without changing active hypothesis protocols."""

import threading

import judge

context = threading.local()
original_validate = judge.validate_verdict
original_judge_one = judge.judge_one


def canonical_name(name):
    return name.strip().strip('`').removeprefix("_root_.")


def validate(verdict, ind):
    original_validate(verdict, ind)
    if verdict["verdict"] == "none_found":
        if any(verdict[k] for k in ["mathlib_declaration", "file", "derivation", "proof_uses_it"]):
            raise ValueError("Negative duplicate verdict must have empty match fields")
    else:
        if any(not verdict[k].strip() for k in ["mathlib_declaration", "file", "derivation"]):
            raise ValueError("Duplicate finding needs a declaration, file and derivation")
        target = context.sample
        if target["lib"] == "mathlib" and canonical_name(verdict["mathlib_declaration"]) == \
                canonical_name(target["name"]):
            raise ValueError("A Mathlib theorem cannot count itself as a duplicate")


def judge_one(sample, *args, **kwargs):
    context.sample = sample
    try:
        return original_judge_one(sample, *args, **kwargs)
    finally:
        del context.sample


if __name__ == "__main__":
    judge.validate_verdict = validate
    judge.judge_one = judge_one
    judge.main()
