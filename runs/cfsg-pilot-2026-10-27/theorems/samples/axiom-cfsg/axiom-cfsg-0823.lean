public noncomputable section

namespace CFSG.LieType.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.RootSystem Matrix

namespace RootSpace

variable {τ : Tag}

theorem ofLattice_single_ne_zero (i : Fin τ.rank) :
    ofLattice (Pi.single i 1 : Fin τ.rank → ℤ) ≠ 0 := fun h => by
  simpa using congrArg (fun x : RootSpace τ => x i) h

end RootSpace
end CFSG.LieType.Chevalley
end
