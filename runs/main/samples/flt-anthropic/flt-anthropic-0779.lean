namespace P2MW.S_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight

attribute [-instance] instTopologicallyFGOfFiniteType

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

universe u

noncomputable section

open MvPowerSeries

open CerednikDrinfeld CerednikDrinfeld.SpecialFormal CerednikDrinfeld.FormalODModule

namespace R4HeightHom

section Frame

variable {r : ℕ} [hr : Fact r.Prime] {K : Type u} [Field K] [CharP K r]

variable (Φ : FormalODModule r K)

variable {Φ}

variable (E : Λ Φ →+* Matrix (Fin 2) (Fin 2) ℚ_[r]) (hinj : Function.Injective E) (m : ℕ)
  (hm : ∀ A : Matrix (Fin 2) (Fin 2) ℤ_[r], ∃ e, E e = (r : ℚ_[r]) ^ m • A.map ((↑) : ℤ_[r] → ℚ_[r]))
  (hΦ4 : Φ.HasHeight 4)

include hinj hΦ4 in

theorem ν₀_coe (e : Λ Φ) (g : Matrix.GeneralLinearGroup (Fin 2) ℚ_[r])
    (hg : (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) = E e) :
    ν₀ E m hm g = hgt e ∧ Module.Finite K (Ker e) ∧
      ∀ (κ : Type u) [Field κ] (f : K →+* κ),
        Module.finrank κ (KerAlgebra (Series.map f (ser e))) = r ^ hgt e := by
  have he : E e = (r : ℚ_[r]) ^ 0 • (g : Matrix (Fin 2) (Fin 2) ℚ_[r]) := by rw [pow_zero, one_smul, hg]
  have hfin : Module.Finite K (Ker e) := finite_ker_of_isUnit E hinj m hm hΦ4 e (hg ▸ Units.isUnit g)
  refine ⟨?_, hfin, fun κ _ f => finrank_fibre e hfin κ f⟩
  rw [ν₀_eq E hinj m hm hΦ4 g e 0 he]
  simp

end Frame
end R4HeightHom
end
end P2MW.S_CerednikDrinfeld_FormalODModule_exists_monoidHom_generalLinearGroup_finrank_kerAlgebra_eq_pow_of_hasHeight
