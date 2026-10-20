namespace P2MW.S_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

open scoped TensorProduct

open Function CartierDual

universe u v

namespace Deformation

namespace WittFirstCoord

p2m_open

section AnnVHopf

variable {k : Type u} [Field k] [PerfectField k] {p : ℕ} [hp : Fact p.Prime] [CharP k p]

variable {A : Type v} [CommRing A] [HopfAlgebra k A] [Module.Finite k A] [Coalgebra.IsCocomm k A]

scoped instance instHopfAlgebraAnnV : HopfAlgebra k ↥(annV k p A) :=
  (isHopfSubalgebra_annV (k := k) (p := p) (A := A)).hopfAlgebra

scoped instance instModuleFiniteAnnV : Module.Finite k ↥(annV k p A) :=
  Module.Finite.of_injective (annV k p A).val.toLinearMap Subtype.val_injective

scoped instance instIsCocommAnnV : Coalgebra.IsCocomm k ↥(annV k p A) where
  comm_comp_comul := by
    ext s
    apply HopfAlgebra.IsHopfSubalgebra.ι₂_injective (K := annV k p A)
    rw [LinearMap.comp_apply, LinearEquiv.coe_coe, HopfAlgebra.IsHopfSubalgebra.ι₂_eq_map,
      HopfAlgebra.HopfKerHopf.map_comm, ← HopfAlgebra.IsHopfSubalgebra.ι₂_eq_map,
      (isHopfSubalgebra_annV (k := k) (p := p) (A := A)).ι₂_comul, Coalgebra.comm_comul]

scoped instance instIsHopfTowerAnnV : HopfAlgebra.IsHopfTower k ↥(annV k p A) A :=
  (isHopfSubalgebra_annV (k := k) (p := p) (A := A)).isHopfTower

@[scoped simp] theorem res_apply (φ : CartierDual k A) (s : ↥(annV k p A)) : res k p A φ s = φ (s : A) := rfl

end AnnVHopf
end WittFirstCoord
end Deformation
end
end P2MW.S_Deformation_exists_mem_wittHom_coeff_zero_eq_iff_of_forall_convPow_eq_zero
