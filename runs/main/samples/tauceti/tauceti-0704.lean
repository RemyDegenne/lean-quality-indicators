public section

open scoped Pointwise

namespace TauCeti

universe u v

section Representations

variable {k G : Type u} [Field k] [Group G] {H K : Subgroup G}

open scoped Classical in
theorem finrank_hom_indFDRep_mackey [Finite G] (A : FDRep k H) (B : FDRep k K) :
    Module.finrank k (indFDRep A ⟶ indFDRep B) =
      letI := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
      ∑ D : DoubleCoset.Quotient (H : Set G) (K : Set G),
        Module.finrank k (Subgroup.resFDRep ((mackeySubgroup D.out K H).subgroupOf H) A ⟶
          (Action.res (FGModuleCat k) (mackeyToH D.out K H)).obj B) := by
  let := Fintype.ofFinite (DoubleCoset.Quotient (H : Set G) (K : Set G))
  rw [(FDRep.indHomMackeyLinearEquiv A B).finrank_eq, Module.finrank_pi_fintype]

end Representations
end TauCeti
end
