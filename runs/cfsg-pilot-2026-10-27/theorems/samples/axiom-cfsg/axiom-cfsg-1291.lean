public section

namespace CFSG.ComponentClassification.RankTwoClassical.ORigid

open Matrix QuadraticMap Subgroup CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Spin

open scoped MatrixGroups

section Step

variable {K : Type} [Field K] [CharP K 2] {ι₂ ι : Type} [Fintype ι₂] [DecidableEq ι₂]
  [Fintype ι] [DecidableEq ι] (oe : ι₂ ⊕ (Fin 2 ⊕ Fin 2) ≃ ι) (Q₂ : QuadraticForm K (ι₂ → K))

variable {oe Q₂} {S₂ : Subgroup (GL ι₂ K)}

variable {Q : QuadraticForm K (ι → K)}
  (hQ : ∀ v, Q v = Q₂ (fun a => v (oe (.inl a))) + StatedQuadPlus 2 K (fun b => v (oe (.inr b))))

include hQ

theorem isPGroup_oSylStep (hS₂ : S₂ ≤ StatedOmega ⇑Q₂) (hS₂p : IsPGroup 2 S₂) :
    IsPGroup 2 (oSylStep oe Q₂ S₂) :=
  isPGroup_oQE.to_sup_of_normal_left' (isPGroup_oSylLevi oe hS₂p)
    (oSylLevi_le_normalizer hQ hS₂)

end Step
end CFSG.ComponentClassification.RankTwoClassical.ORigid
end
