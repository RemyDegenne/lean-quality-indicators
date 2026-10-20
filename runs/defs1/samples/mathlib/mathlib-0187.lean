@[expose] public section

open CategoryTheory Functor

variable {C D : Type*} [Category* C] [Category* D]

variable (F : C ⥤ D) (G : D ⥤ C) (H : C ⥤ D)

namespace CategoryTheory.Adjunction.Triple

variable {F G H} (t : Triple F G H)

/--
Given an adjoint triple `F ⊣ G ⊣ H`, the left adjoint `F` is fully faithful if and only if the
right adjoint `H` is fully faithful.
-/
noncomputable def fullyFaithfulEquiv : F.FullyFaithful ≃ H.FullyFaithful where
  toFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₂.counit := by
      rw [← t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₂.fullyFaithfulROfIsIsoCounit
  invFun h :=
    haveI := h.full
    haveI := h.faithful
    haveI : IsIso t.adj₁.unit := by
      rw [t.isIso_unit_iff_isIso_counit]
      infer_instance
    t.adj₁.fullyFaithfulLOfIsIsoUnit
  left_inv _ := Subsingleton.elim _ _
  right_inv _ := Subsingleton.elim _ _

end CategoryTheory.Adjunction.Triple
end
