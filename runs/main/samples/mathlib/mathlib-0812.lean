@[expose] public section

universe v₁ v₂ u₁ u₂

variable {C : Type u₁}

namespace CategoryTheory

open CategoryTheory.MonoidalCategory

namespace MonoidalOpposite

@[inherit_doc]
notation:max C "ᴹᵒᵖ" => MonoidalOpposite C

theorem mop_injective : Function.Injective (mop : C → Cᴹᵒᵖ) := @mop.inj C

end MonoidalOpposite
end CategoryTheory
end
