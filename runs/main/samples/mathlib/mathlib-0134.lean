@[expose] public section

universe u

namespace ZFClass

variable {A B C : ZFClass.{u}} {x y : ZFSet.{u}}

@[inherit_doc]
scoped notation:50 A:50 " ᶜ∈ " B:50 => ZFClass.CMem A B

scoped notation:50 A:50 " ᶜ∉ " B:50 => ¬ ZFClass.CMem A B

@[inherit_doc]
scoped prefix:110 "⋃₀ " => ZFClass.sUnion

@[inherit_doc]
scoped prefix:110 "⋂₀ " => ZFClass.sInter

@[simp, norm_cast]
lemma coe_powerset (x : ZFSet.{u}) : ↑x.powerset = powerset.{u} x := by ext; simp

end ZFClass
end
