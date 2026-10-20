@[expose] public section

open UpperHalfPlane hiding I

open scoped Real Topology

open Filter Complex Asymptotics

variable {Γ : Subgroup (GL (Fin 2) ℝ)} [Γ.IsArithmetic]
  {k : ℤ} (hk : 0 < k) {F : Type*} [FunLike F ℍ ℂ] (f : F) {s : ℂ}

local notation "h" => Subgroup.strictWidthInfty

open ConjAct Pointwise in
private local instance :
    Subgroup.IsArithmetic (toConjAct (ModularGroup.S : GL (Fin 2) ℝ)⁻¹ • Γ) := by
  convert Subgroup.IsArithmetic.conj Γ ↑(ModularGroup.S⁻¹)
  simp only [ModularGroup.S_inv, ← map_inv]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [ModularGroup.S]

open ModularForm

namespace CuspForm

variable [CuspFormClass F Γ k]

lemma Λ_eq_mellin : Λ hk f = mellin (fun t ↦ f (ofComplex (I * t))) :=
  (isStrongFEPair hk f).Λ_eq

end CuspForm
end
