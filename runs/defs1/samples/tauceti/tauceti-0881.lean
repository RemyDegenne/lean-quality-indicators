public section

open CategoryTheory

namespace TauCeti

universe uR uA uM

variable {R : Type uR} {A : Type uA} [CommRing R] [Ring A] [Algebra R A]
  {𝒜 : ℤ → Submodule R A} [GradedAlgebra 𝒜] {d : A →ₗ[R] A}

namespace DGRightModuleCat

attribute [instance] addCommGroup moduleBase moduleOp scalarTower decomposition gradedSMul

variable {h : IsDGAlgebra 𝒜 d}

variable {M N P : DGRightModuleCat.{uR, uA, uM} h}

/-- Forget the grading, differential, and algebra action of a DG right module. -/
@[expose]
def forgetToModuleCat : DGRightModuleCat.{uR, uA, uM} h ⥤ ModuleCat.{uM} R where
  obj M := ModuleCat.of R M
  map f := ModuleCat.ofHom (f.toLinearMap.restrictScalars R)
  map_id M := by
    apply ModuleCat.hom_ext
    ext x
    exact DGRightModuleHom.id_apply M.isDGRightModule x
  map_comp f g := by
    apply ModuleCat.hom_ext
    ext x
    exact DGRightModuleHom.comp_apply g f x

end DGRightModuleCat
end TauCeti
end
