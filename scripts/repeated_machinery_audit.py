"""Review repeated arguments on the existing file sample."""

import file_audits


if __name__ == "__main__":
    file_audits.RUBRICS = ["repeated-proof-machinery"]
    file_audits.main()
