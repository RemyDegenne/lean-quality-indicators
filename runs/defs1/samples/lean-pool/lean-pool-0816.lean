@[expose] public section

namespace AtanasovRanganathan.GenusFiveRow06FixedCover

open Utilities

open Certificate ExplicitPotential

open Certificate.ExplicitPotential

open Certificate.AffineCover

open GenusFiveCoreAtlas GenusFiveClosedCover Configurations

open GenusFiveRow06CoverBase

open GenusFiveRow06Symmetry (Chamber chamber_covers)

/-- Subtree splitting on `2 * length[2] - 2 * length[3]` in the row-06 symmetry chamber, with
leaves selecting cells 116, 117, 118, 119, 120 and Farkas receipts excluding inconsistent sign
branches. -/
def treePart33 : CompactCellTree :=
  .split 14
    (.cell 116 [190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 205, 446, 206,
      238, 318, 319, 208, 328])
    (.split 15
        (.cell 117 [212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 227, 228, 241,
          321, 322, 230, 447])
        (.split 27
            (.cell 118 [242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 272, 273,
              257, 258, 261, 324, 325, 260, 448])
            (.split 28
                (.cell 119 [277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 449,
                  450, 292, 293, 522, 355, 356, 295, 451])
                (.split 29
                    (.cell 120 [367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379,
                      452, 453, 388, 381, 523, 383, 384, 385, 454])
                    (.absurd 455)))))

end AtanasovRanganathan.GenusFiveRow06FixedCover
end
