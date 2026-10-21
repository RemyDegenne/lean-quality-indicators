"""Blind reproduction of the four file-audit rubrics selected for follow-up.

Uses the original prompts, file sample and evidence validator. Restricting the
suite here makes reports and completion markers refer to the 120 selected reviews.
"""

import file_audits


if __name__ == "__main__":
    file_audits.RUBRICS = ["statement-generality", "vacuity-and-misstatement",
                          "simp-interface", "readable-proof-simplification"]
    file_audits.main()
