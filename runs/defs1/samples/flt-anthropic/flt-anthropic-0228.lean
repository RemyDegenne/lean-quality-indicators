open scoped TensorProduct

attribute [instance] GaloisRepAdic.instAddCommGroup GaloisRepAdic.instModule
  GaloisRepAdic.instFree GaloisRepAdic.instFinite

namespace GaloisRepAdic

variable {A : Type} [CommRing A] [IsLocalRing A]

def ofResidualGaloisRep {k : Type} [Field k] (ρ : ResidualGaloisRep k) : GaloisRepAdic k :=
  { V := ρ.V
    finrank_eq := ρ.finrank_eq
    ρ := ρ.ρ
    isAdicContinuous := by
      intro n
      obtain ⟨L, hL, h1⟩ := ρ.factorsThroughFiniteLevel
      refine ⟨L, hL, fun σ hσ v => ?_⟩
      rw [h1 σ hσ, Module.End.one_apply, sub_self]
      exact Submodule.zero_mem _ }

end GaloisRepAdic
