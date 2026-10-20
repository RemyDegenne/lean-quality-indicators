public section

open CategoryTheory

namespace TauCeti.UniversalEnvelopingAlgebra

universe u w

attribute [local instance high] Algebra.toModule

variable {L : Type u} [LieRing L] [LieAlgebra ℚ L]

variable {I : Type w} {κ : Type*}

variable {V : Type} [AddCommGroup V] [Module ℚ V]

variable (e : I → L) (h : κ → L)

variable (ρ : _root_.UniversalEnvelopingAlgebra ℚ L →ₐ[ℚ] Module.End ℚ V)

variable (M : AddSubgroup V)

variable (hM : ∀ u ∈ kostantForm e h, ∀ m ∈ M, ρ u m ∈ M)

variable (hnil : ∀ i, IsNilpotent (ρ (_root_.UniversalEnvelopingAlgebra.ι ℚ (e i))))

variable {n : ℕ} (b : Module.Basis (Fin n) ℤ M)

variable (A : Type*) [CommRing A]

/-- The base change of the Chevalley carrier is the quotient of the base-changed general-linear
coordinate algebra by the base-changed defining ideal: base change of the group scheme and of its
presentation as a closed subgroup scheme agree. -/
noncomputable def kostantGeneratedBaseChangeIso :
    CommHopfAlgCat.quotient
        (CommHopfAlgCat.baseChange (K := A) (GeneralLinear.coordinateHopfAlgebra ℤ n))
        (kostantGeneratedBaseChangeIdeal e h ρ M hM hnil b A) ≅
      CommHopfAlgCat.baseChange (K := A)
        (CommHopfAlgCat.quotient (GeneralLinear.coordinateHopfAlgebra ℤ n)
          (kostantGeneratedDefiningIdeal e h ρ M hM hnil b)) :=
  CommHopfAlgCat.quotientBaseChangeIso (kostantGeneratedDefiningIdeal e h ρ M hM hnil b)

end TauCeti.UniversalEnvelopingAlgebra
end
