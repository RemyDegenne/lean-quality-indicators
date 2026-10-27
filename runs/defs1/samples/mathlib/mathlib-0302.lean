@[expose] public section

namespace CategoryTheory

namespace Bicategory

universe w v u

variable {B : Type u} [Bicategory.{w, v} B]

@[inherit_doc] scoped notation "ε" => Comonad.counit

@[inherit_doc] scoped notation "ε[" x "]" => Comonad.counit (t := x)

@[inherit_doc] scoped notation "Δ" => Comonad.comul

@[inherit_doc] scoped notation "Δ[" x "]" => Comonad.comul (t := x)

namespace OplaxTrans

namespace ComonadBicat

open scoped Oplax.OplaxTrans.OplaxFunctor in
scoped instance : Bicategory (ComonadBicat B) :=
  inferInstanceAs <| Bicategory (LocallyDiscrete (Discrete PUnit) ⥤ᵒᵖᴸ B)

/-- The object in `B` associated with the comonad. -/
def obj (m : ComonadBicat B) :=
  m.toOplax.obj ⟨⟨PUnit.unit⟩⟩

end ComonadBicat
end OplaxTrans
end Bicategory
end CategoryTheory
end
