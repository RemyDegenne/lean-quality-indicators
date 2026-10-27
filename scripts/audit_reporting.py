"""Reporting readiness, separate from the frozen inference protocols."""

APPENDIX_AUDITS = {
    "concept-reinvention": (
        "Source review found permitted wrappers and deliberate representations flagged, "
        "along with internal-project duplication outside the rubric's Mathlib scope."
    ),
    "simp-interface": (
        "Source review found useful API additions mixed with objections to harmless "
        "overlapping rules and claims lacking a demonstrated simplification problem."
    ),
}


def is_main_audit(audit):
    return audit not in APPENDIX_AUDITS


def reporting_status(audit):
    if is_main_audit(audit):
        return {"placement": "main"}
    return {"placement": "appendix", "readiness": "not_ready_for_use",
            "reason": APPENDIX_AUDITS[audit]}
