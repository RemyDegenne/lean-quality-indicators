@[expose] public section

namespace LO

namespace Modal

macro_rules | `(tactic| trivial) => `(tactic|
    first
    | apply mem_origin <| by assumption
    | apply mem_imp₁ <| by assumption
    | apply mem_imp₂ <| by assumption
  )

namespace Hilbert

namespace Grz

namespace Kripke

open Formula

open Formula.Kripke

open Entailment

open Entailment.Context

open ComplementClosedConsistentFinset

variable {φ ψ : Formula ℕ}

lemma truthlemma_lemma3 : (Hilbert.Grz) ⊢! (φ ⋏ □(φ ==> □φ)) ==> □φ := by
  apply KT_weakerThan_Grz.pbl;
  by_contra hC;
  have := (not_imp_not.mpr <| Hilbert.KT.Kripke.complete |>.complete) hC;
  simp only [ValidOnFrameClass.models_iff] at this;
  obtain ⟨F, F_refl, hF⟩ := ValidOnFrameClass.exists_frame_of_not this;
  simp only [Semantics.Realize, ValidOnFrame, ValidOnModel, Satisfies,
    LogicalConnective.Prop.arrow_eq, imp_false, not_forall, not_exists, not_not] at hF;
  obtain ⟨V, x, ⟨⟨h₁, h₂⟩, ⟨y, ⟨Rxy, h₃⟩⟩⟩⟩ := hF;
  have := h₂ x (F_refl.refl x);
  simp_all

end Kripke
end Grz
end Hilbert
end Modal
end LO
end
