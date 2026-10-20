@[expose] public section

universe v u

open CategoryTheory Limits

variable {C : Type u} [Category.{v} C] [HasZeroMorphisms C]

namespace CochainComplex

variable {K K' K'' : ChainComplex C ℕ} {L L' L'' : CochainComplex C ℕ}

namespace ConnectData

variable (h : ConnectData K L) (h' : ConnectData K' L') (h'' : ConnectData K'' L'')

open HomologicalComplex

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
/-- If `h : ConnectData K L`, then `h.cochainComplex` identifies to `K` in degrees `≤ -1`. -/
@[simps!]
def restrictionLEIso :
    h.cochainComplex.restriction (ComplexShape.embeddingUpIntLE (-1)) ≅ K :=
  Hom.isoOfComponents
    (fun n ↦ h.cochainComplex.restrictionXIso (ComplexShape.embeddingUpIntLE (-1))
        (i := n) (i' := .negSucc n) (by dsimp; lia)) (by
    rintro _ n rfl
    rw [restriction_d_eq (e := (ComplexShape.embeddingUpIntLE (-1))) _
      (i' := Int.negSucc (n + 1)) (j' := Int.negSucc n) (by dsimp; lia) (by dsimp; lia),
      cochainComplex_d, d_negSucc]
    simp)

end ConnectData
end CochainComplex
end
