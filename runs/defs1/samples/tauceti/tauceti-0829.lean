public section

open CategoryTheory MonoidalCategory

namespace TauCeti

namespace AlgebraicGeometry

open _root_.AlgebraicGeometry _root_.AlgebraicGeometry.Scheme.Modules

universe u

noncomputable section

variable {T Y : Scheme.{u}} {s : T ⟶ Y}

namespace RigidifiedLineBundle

section Automorphisms

variable (P : RigidifiedLineBundle s)

/-- The automorphisms of the line bundle underlying a rigidified line bundle `P` that respect
its rigidification: those whose pullback along `s` carries the trivialization to itself. -/
def autSubgroup : Subgroup (Aut P.lineBundle.obj) where
  carrier := {e | (Scheme.Modules.pullback s).map e.asIso.hom ≫ P.rigidification.hom =
    P.rigidification.hom}
  one_mem' := by
    rw [Set.mem_ofPred_eq]
    -- The unit of `Aut` is the identity isomorphism; Mathlib has no lemma for its `hom`.
    have hone : (1 : Aut P.lineBundle.obj).asIso.hom = 𝟙 _ := rfl
    rw [hone, CategoryTheory.Functor.map_id, Category.id_comp]
  mul_mem' {e e'} he he' := by
    rw [Set.mem_ofPred_eq] at he he' ⊢
    have hmul : (e * e').asIso.hom = e'.asIso.hom ≫ e.asIso.hom :=
      (congrArg Iso.hom (Aut.mul_asIso _ e e')).trans (Iso.trans_hom e'.asIso e.asIso)
    rw [hmul, Functor.map_comp, Category.assoc, he, he']
  inv_mem' {e} he := by
    rw [Set.mem_ofPred_eq] at he ⊢
    have hinv : (e⁻¹).asIso.hom = e.asIso.inv :=
      (congrArg Iso.hom (Aut.inv_asIso _ e)).trans (Iso.symm_hom e.asIso)
    rw [hinv]
    conv_lhs => rw [← he]
    rw [← Category.assoc, ← Functor.map_comp, e.asIso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp]

end Automorphisms
end RigidifiedLineBundle
end
end AlgebraicGeometry
end TauCeti
end
