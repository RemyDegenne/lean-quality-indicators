@[expose] public section

universe v u

open CategoryTheory

open LinearMap MonObj

open scoped TensorProduct

attribute [local ext] TensorProduct.ext

namespace ModuleCat

variable {R : Type u} [CommRing R]

namespace MonModuleEquivalenceAlgebra

scoped[ModuleCat.MonModuleEquivalenceAlgebra] attribute [instance] MonObj.toRing

scoped instance Algebra_of_Mon_ (A : ModuleCat.{u} R) [MonObj A] : Algebra R A where
  algebraMap :=
  { η[A].hom with
    map_zero' := η[A].hom.map_zero
    map_one' := rfl
    map_mul' := fun x y => by
      have h := congr($(ModuleCat.hom_ext_iff.mp (one_mul A).symm) (x ⊗ₜ η[A] y))
      rwa [MonoidalCategory.leftUnitor_hom_apply, ← η[A].hom.map_smul] at h }
  commutes' := fun r a => by
    dsimp
    have h₁ := congr($(ModuleCat.hom_ext_iff.mp (one_mul A)) (r ⊗ₜ a))
    have h₂ := congr($(ModuleCat.hom_ext_iff.mp (mul_one A)) (a ⊗ₜ r))
    exact h₁.trans h₂.symm
  smul_def' := fun r a =>
    congr($(ModuleCat.hom_ext_iff.mp (one_mul A)) (r ⊗ₜ a)).symm

attribute [local instance] inverseObj

/-- Converting a bundled algebra to a monoid object in `ModuleCat R`.
-/
@[simps]
def inverse : AlgCat.{u} R ⥤ Mon (ModuleCat.{u} R) where
  obj A := { X := ↧A, mon := inverseObj A }
  map f :=
    { hom := ofHom f.hom.toLinearMap
      isMonHom_hom.one_hom := hom_ext <| LinearMap.ext f.hom.commutes
      isMonHom_hom.mul_hom := hom_ext <| TensorProduct.ext <| LinearMap.ext₂ <| map_mul f.hom }

end MonModuleEquivalenceAlgebra
end ModuleCat
end
