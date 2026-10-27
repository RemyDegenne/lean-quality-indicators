@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Opposite

namespace Limits

variable {J : Type u} [Category.{v} J] {C : Type u'} [Category.{v'} C]
  (F : Jᵒᵖ ⥤ J ⥤ C)

namespace Wedge

variable {F}

section Constructor

variable (pt : C) (π : ∀ (j : J), pt ⟶ (F.obj (op j)).obj j)
  (hπ : ∀ ⦃i j : J⦄ (f : i ⟶ j), π i ≫ (F.obj (op i)).map f = π j ≫ (F.map f.op).app j)

/-- Constructor for wedges. -/
abbrev mk : Wedge F :=
  Multifork.ofι _ pt π (fun f ↦ hπ f.hom)

end Constructor
end Wedge
end Limits
end CategoryTheory
end
