namespace OAI

noncomputable section

namespace Tachikawa

open CategoryTheory CategoryTheory.Limits

open scoped ModuleCat.Algebra

variable {k R : Type} [Field k] [Ring R] [Algebra k R]
  {I : Type} (F : I → ModuleCat R) (N : ModuleCat R)

variable {J : Type} [Finite J] (G : J → ModuleCat k)

lemma coproductPiEquiv_ι_ne {i j : J} (h : i ≠ j) (x : G i) :
    coproductPiEquiv G (Sigma.ι G i x) j = 0 := by
  rw [coproductPiEquiv_ι, biproduct.ι_π_ne _ h]
  rfl

end Tachikawa
end
end OAI
