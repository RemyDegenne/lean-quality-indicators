namespace OAI

section

namespace PlanarL1.Columns.Model.MainCell

open PlanarL1.Interpolation

open scoped NNReal

variable {n : ℕ} {M : Model n} {I J : Set ℝ} {root : Fin n}

variable (F : M.Field I 1) (hJI : J ⊆ I)

variable (R : Point.RadialTree (M := M) (J := J) (root := root)) (q : ℝ)

variable (C : Cell R q)

lemma namedReplacement_near_frontier (hJ : IsCompact J) (v x z : M.Point J root)
    {α : Point.RadialTree.Noise (n := n)} (hα : R.NoiseBounds α)
    {E : ℝ} (hE : 0 ≤ E) (hδ : R.δ = E/8) (β lo : ℝ)
    (hz : z ∈ boundary R q C) (hd : 2*dist x z < 3*E) :
    namedReplacement F hJI R q C v α E β lo x = ⟨0,old F hJI x⟩ := by
  apply clippedNamed_retains
  change proposal F hJI R q C v α E x < old F hJI x
  have hm := frontier_margin F hJI R q C hJ v hα hE hδ hz
  have hxz := (proposal_lipschitz F hJI R q C v hα E).dist_le_mul x z
  have hs := (old_lipschitz F hJI R).dist_le_mul z x
  simp only [Real.dist_eq,NNReal.coe_one,one_mul] at hxz hs
  rw [dist_comm z x] at hs
  have hp := (abs_le.mp hxz).2
  have ho := (abs_le.mp hs).2
  linarith

end PlanarL1.Columns.Model.MainCell
end
end OAI
