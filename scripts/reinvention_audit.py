"""Run the concept audit alone on the existing file sample, with separate reports."""

import file_audits


if __name__ == "__main__":
    file_audits.RUBRICS = ["concept-reinvention"]
    file_audits.main()
