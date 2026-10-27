public section

namespace CFSG.ClassicalGroups.Orthogonal.OmegaSiegel

open CFSG.HardMathSupport.Kantor79 CFSG.ClassicalGroups.Orthogonal.SiegelRT1

open CFSG.RankThree.GF2n.Smith81 QuadraticMap Module

variable {K' : Type*} [Field K'] [CharP K' 2] [Finite K'] {N : Type*} [AddCommGroup N]
  [Module K' N] [FiniteDimensional K' N] {QN : QuadraticForm K' N} {K : Type*} [Field K]
  [CharP K 2] [Finite K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Qf : QuadraticForm K V} {ρ : ↥(elementaryGroup QN) →* (V ≃ₗ[K] V)}

theorem OmegaSetting.caseII_of_six_lt_finrank (hs : OmegaSetting QN Qf ρ)
    (htop : commutatorSpace ρ.range = ⊤) {e f p p' u v : N} (hF : MinusThreeFrame QN e f p p' u v)
    (h6 : 6 < finrank K V) :
    ∀ a b c, IsFlag QN a b c → movedSpace (rhoE ρ a b) ⊓ movedSpace (rhoE ρ a c) = ⊥ :=
  (hs.flag_dichotomy hF).resolve_left fun hI => by
    have := hs.finrank_le_six_of_caseI htop hF hI
    omega

end CFSG.ClassicalGroups.Orthogonal.OmegaSiegel
end
