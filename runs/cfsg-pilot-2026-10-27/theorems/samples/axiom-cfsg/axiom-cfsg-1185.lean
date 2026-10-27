public noncomputable section

namespace CFSG.LieType.Steinberg.Sp

open Matrix CFSG.LieType.Universal CFSG.LieType.Universal.Symplectic
  CFSG.LieType.Universal.Symplectic.SpExtras CFSG.LieType.RootSystem TauCeti.GLSymplecticFin

variable {n : ℕ} {F : Type} [Field F]

theorem redundantR2 [Finite F] (hn : 2 ≤ n) : RedundantR2 (Φ n F) (rootDatum n F).rootGroup :=
  redundantR2_of rfl (fun O => ⟨commC, commutatorFormula O⟩)
    (fun O C hC => chevalleyExtras hn O C hC)
    (bijective_stPi_of (isCTGroupDatum n F) (steinbergExtras n F)).2

end CFSG.LieType.Steinberg.Sp
end
