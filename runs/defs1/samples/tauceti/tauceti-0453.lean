public section

open CategoryTheory

namespace TauCeti

open GradedLinearQuiver

universe v u

namespace DGCategory

variable (R : Type v) [CommRing R] (C : Type u) [DGCategory R C]

variable {R C}

variable (R C)

/-- The DG functor from the differential graded category of the `A∞` category of a differential
graded category `C` back to `C`: the identity on objects, sending `homLof f` to `f`. -/
-- The body is exposed for the same reason as that of `toAInfinityDGFunctor`.
@[expose]
noncomputable def ofAInfinityDGFunctor :
    EnrichedFunctor (CochainComplex (ModuleCat.{v} R) ℤ) (AInfinityDG R C) C :=
  EnrichedFunctor.ofDGMap (fun X ↦ X.as) (fun n ↦ (aInfinityDGHomEquiv _ _ n).symm.toLinearMap)
    (fun {X Y} n g ↦ by
      obtain ⟨f, rfl⟩ := (aInfinityDGHomEquiv X.as Y.as n).surjective g
      simp only [LinearEquiv.coe_coe]
      rw [← aInfinityDGHomEquiv_dgDifferential, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply])
    (fun X ↦ by
      simp only [LinearEquiv.coe_coe]
      rw [← aInfinityDGHomEquiv_dgId, LinearEquiv.symm_apply_apply])
    (fun {X Y Z p q n} f g h ↦ by
      obtain ⟨f, rfl⟩ := (aInfinityDGHomEquiv X.as Y.as p).surjective f
      obtain ⟨g, rfl⟩ := (aInfinityDGHomEquiv Y.as Z.as q).surjective g
      simp only [LinearEquiv.coe_coe]
      rw [← aInfinityDGHomEquiv_dgComp, LinearEquiv.symm_apply_apply,
        LinearEquiv.symm_apply_apply, LinearEquiv.symm_apply_apply])

end DGCategory
end TauCeti
end
