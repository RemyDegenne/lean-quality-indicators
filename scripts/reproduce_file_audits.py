"""Blind reproduction of all six current file-audit rubrics.

Uses the original prompts, file sample and evidence validator. Restricting the
suite here makes reports and completion markers refer to the 180 selected reviews.
"""

import file_audits


if __name__ == "__main__":
    file_audits.RUBRICS = ["statement-generality", "vacuity-and-misstatement",
                          "simp-interface", "readable-proof-simplification",
                          "concept-reinvention", "repeated-proof-machinery"]
    file_audits.main()
