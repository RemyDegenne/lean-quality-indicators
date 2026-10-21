namespace OAI

namespace PureTypeSystem.Labelled

universe u

variable {S : Type u} {P : Specification S}

namespace SpecializedCode

section

variable {Γ : List (Expr S)} {γ : Nat → Mode} {C : Set (Set S)}
    (B : SpecializedCode S) (L : LogicSetup P Γ γ C) (I J k p n g j h : Set S)

namespace Formed

variable {B L I J k p n g j h} (H : B.Formed L I J k p n g j h)
    (KY : QuantifierRoute L.witnesses C L.base j) (KP : QuantifierRoute L.witnesses C L.base h)

include H

theorem eAt_formula {v x : Expr S} (t : Fin 3) 
    (hv : HasType P Γ v B.predType) (mv : WellModed γ v .data)
    (hx : HasType P Γ x B.xType) (mx : WellModed γ x .data)
    : L.Formula (B.eAt L.code KY.code KP.code t v x) := by
  obtain ⟨s,hs⟩ := KY.triple.domain.1
  exact L.all_formula_family KY H.y_sorted H.y_mode (H.y_sorted s hs) (H.eAtBody_family KY KP t hv mv hx mx)

end Formed
end
end SpecializedCode
end PureTypeSystem.Labelled
end OAI
