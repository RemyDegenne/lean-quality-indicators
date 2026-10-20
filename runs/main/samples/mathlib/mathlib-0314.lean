@[expose] public noncomputable section

open ModularForm Complex Filter Function Matrix.SpecialLinearGroup Metric Set

open UpperHalfPlane hiding I

open scoped Real MatrixGroups CongruenceSubgroup Topology Manifold

variable {k : ℤ} {F : Type*} [FunLike F ℍ ℂ] {Γ : Subgroup (GL (Fin 2) ℝ)} {h : ℝ} (f : F)

local notation "I∞" => comap Complex.im atTop

local notation "𝕢" => Periodic.qParam

namespace UpperHalfPlane

lemma IsZeroAtImInfty.valueAtInfty_eq_zero {f : ℍ → ℂ} (hf : IsZeroAtImInfty f) :
    valueAtInfty f = 0 :=
  hf.limUnder_eq

end UpperHalfPlane
end
