public section

namespace CFSG.GH74.GLS.C3.Layer1.Thm1P38

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.IVK CFSG.GH74.GLS.C3.Layer1
  CFSG.GH74.GLS.C3.Layer1.Thm1

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {x y : G} {K T V W : Subgroup G} {f z : G}

namespace Env37

variable (E : Env37 x y K T V W f z) (D : L37Data x K T f z)

include E

theorem hEP : ∀ e ∈ zpowers f ⊔ zpowers x, ∀ p ∈ T ⊓ K, e * p = p * e := by
  intro e he p hp
  have hle : zpowers f ⊔ zpowers x ≤ centralizer ({p} : Set G) :=
    sup_le (zpowers_le.2 (mem_centralizer_singleton_iff.2 (E.hfP p hp)))
      (zpowers_le.2 (mem_centralizer_singleton_iff.2 (E.hxc p hp.1).symm))
  exact mem_centralizer_singleton_iff.1 (hle he)

end Env37
end CFSG.GH74.GLS.C3.Layer1.Thm1P38
end
