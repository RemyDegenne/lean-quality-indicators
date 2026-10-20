@[expose] public section

namespace LO

namespace Modal

namespace Kripke

open Formula.Kripke

infix:80 " ⇄ " => Model.Bisimulation

infix:50 " ↭ " => ModalEquivalent

infix:80 " →ₚ " => Frame.PseudoEpimorphism

infix:80 " →ₚ " => Model.PseudoEpimorphism

section «lp_section_4»

infix:100 "↾" => Frame.PointGenerated

namespace Frame

namespace PointGenerated

variable {F : Kripke.Frame} {r : F.World}

lemma rel_universal (F_refl : Std.Refl F.Rel) (F_eucl : Euclidean F.Rel) : Universal (F↾r).Rel := by
  have F_symm := symm_of_refl_eucl F_refl.refl F_eucl;
  rintro ⟨x, (rfl | hx)⟩ ⟨y, (rfl | hy)⟩;
  · exact F_refl.refl _;
  · exact hy;
  · exact F_symm hx;
  · apply F_symm <| F_eucl hx hy;

end PointGenerated
end Frame
end «lp_section_4»
end Kripke
end Modal
end LO
end
