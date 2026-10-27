@[expose] public section

open CategoryTheory

universe u

namespace QuotientAddGroup

variable {V : Type u} [AddCommGroup V] (L : AddSubgroup V) (ℓ : ℤ)

local notation "I" => Ideal.span (Set.singleton ℓ)

local notation "N" n => (I ^ n • ⊤ : Submodule ℤ L)

local notation "Q" => Functor.ofOpSequence
  (X := fun n => ModuleCat.of ℤ (L ⧸ N n))
  (fun n => ModuleCat.ofHom (Submodule.factorPowSucc I L n))

/-- Compatible signed scalar-power torsion sections of `V / L` identify linearly
with the `span {ℓ}`-adic completion of `L`, when multiplication by `ℓ` is bijective
on `V`. At level `n` the coordinate represented by `v` is sent to `[ℓ ^ n • v]`.
The construction composes the natural isomorphism of coordinate diagrams with
Mathlib's completion lift. -/
@[no_expose] noncomputable def scalarTorsionEquivAdicCompletion
    (h : Function.Bijective (zsmulAddGroupHom (α := V) ℓ)) :
    ModuleCat.sectionsSubmodule (Functor.ofOpSequence
  (X := fun n => ModuleCat.of ℤ (AddMonoidHom.ker (zsmulAddGroupHom (α := V ⧸ L) (ℓ ^ n))))
  (fun n => ModuleCat.ofHom
    (AddMonoidHom.toIntLinearMap
      (AddMonoidHom.restrict
        (show Set.MapsTo (zsmulAddGroupHom (α := V ⧸ L) ℓ)
          (AddMonoidHom.ker (zsmulAddGroupHom (α := V ⧸ L) (ℓ ^ (n + 1))))
          (AddMonoidHom.ker (zsmulAddGroupHom (α := V ⧸ L) (ℓ ^ n))) from by
          intro x hx
          change (ℓ ^ n) • (ℓ • x) = 0
          rw [← mul_smul, ← pow_succ]
          exact hx))))) ≃ₗ[ℤ] AdicCompletion I L :=
  (sectionsCongr (coordinateIso L ℓ h)).trans (completionSectionsEquiv L ℓ)

end QuotientAddGroup
end
