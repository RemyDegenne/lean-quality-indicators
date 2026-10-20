public section

open CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w x y z

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {I : Type w} {κ : Type} [Finite κ]

variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)

variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

variable (wt : Fin n → κ → ℤ)

variable (A : Type*) [CommRing A]

theorem map_tmul_mem_kostantToralBaseChangePresentationIdeal_of_mem (s : A)
    {y : GeneralLinear.coordinateHopfAlgebra ℤ n}
    (hy : y ∈ kostantToralDefiningIdeal e h ρ M hM hnil b wt) :
    (GeneralLinear.coordinateHopfAlgebraBaseChangeIso ℤ A n).hom.hom (s ⊗ₜ[ℤ] y) ∈
      kostantToralBaseChangePresentationIdeal e h ρ M hM hnil b wt A := by
  rw [mem_kostantToralBaseChangePresentationIdeal_iff,
    CommHopfAlgCat.inv_hom_apply, kostantToralBaseChangeIdeal_def]
  exact CommHopfAlgCat.tmul_mem_baseChangeHopfIdeal s hy

end TauCeti.UniversalEnvelopingAlgebra
end
