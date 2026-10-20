universe u

public noncomputable section

namespace IGame

/-- Encode a game as an ordered pair of the ZFC sets of recursively encoded options. -/
def toZFSet (x : IGame.{u}) : ZFSet.{u} :=
  IGame.moveRecOn x fun z ih ↦
    ZFSet.pair (ZFSet.range fun y : z.moves left ↦ ih left y.1 y.2)
      (ZFSet.range fun y : z.moves right ↦ ih right y.1 y.2)

end IGame
end
