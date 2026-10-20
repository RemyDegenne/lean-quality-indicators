@[expose] public section

universe v₁ v₂ u₁ u₂

noncomputable section

open CategoryTheory

open CategoryTheory.Functor

open Opposite

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C]

variable {J : Type u₂} [Category.{v₂} J]

variable (X : Type v₂)

section OppositeCoproducts

variable {α : Type*} {Z : α → C}

theorem opCoproductIsoProduct'_inv_comp_inj {c : Cofan Z} {f : Fan (op <| Z ·)}
    (hc : IsColimit c) (hf : IsLimit f) (b : α) :
    (opCoproductIsoProduct' hc hf).inv ≫ (c.inj b).op = f.proj b :=
  IsLimit.conePointUniqueUpToIso_inv_comp (Cofan.IsColimit.op hc) hf ⟨b⟩

end OppositeCoproducts
end CategoryTheory.Limits
end
end
