@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow03FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

/-- Subtree splitting on `- length[1] - length[5] + length[11]` in the row-03 length cone, with
leaves selecting cells 13, 48, 49, 60 and Farkas receipts excluding inconsistent sign branches. -/
def treePart54 : CompactCellTree :=
  .split 52
    (.split 47
        (.split 22
            (.cell 13 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 118, 511,
              512, 126, 123, 406, 362, 122, 363, 117])
            (.split 54
                (.split 17
                    (.cell 48 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178,
                      186, 170, 173, 172, 197, 414, 176])
                    (.absurd 513))
                (.absurd 222)))
        (.split 22
            (.cell 13 [105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 124, 118, 514,
              512, 126, 123, 406, 362, 122, 363, 117])
            (.split 54
                (.split 20
                    (.cell 49 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 176,
                      348, 170, 173, 172, 197, 414, 515, 186])
                    (.absurd 516))
                (.absurd 517))))
    (.split 47
        (.split 54
            (.split 4
                (.cell 60 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 146, 185,
                  141, 144, 145, 148, 409, 518, 152, 147, 143])
                (.split 17
                    (.cell 48 [156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 178,
                      186, 170, 173, 174, 197, 414, 176])
                    (.absurd 513)))
            (.absurd 480))
        (.split 54
            (.split 20
                (.cell 49 [127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 143, 340,
                  141, 144, 145, 148, 409, 509, 185])
                (.absurd 519))
            (.absurd 520)))

end AtanasovRanganathan.GenusFiveRow03FixedCover
end
