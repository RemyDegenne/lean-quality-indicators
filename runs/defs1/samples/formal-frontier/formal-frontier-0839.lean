@[expose] public section

universe u v w x

namespace GroupLike

variable {R : Type u} {C : Type v}

variable [CommSemiring R] [AddCommMonoid C] [Module R C] [Coalgebra R C]

variable {D : Type w} {E : Type x}

variable [AddCommMonoid D] [Module R D] [Coalgebra R D]

variable [AddCommMonoid E] [Module R E] [Coalgebra R E]

/-- Group-like elements of an `R`-coalgebra correspond to coalgebra morphisms from
its canonical scalar coalgebra, by scalar multiplication and evaluation at `1`. -/
noncomputable def coalgHomEquiv : GroupLike R C ≃ (R →ₗc[R] C) where
  toFun g :=
    { LinearMap.toSpanSingleton R C g.val with
      counit_comp := by
        apply LinearMap.ext_ring
        simpa only [LinearMap.comp_apply, LinearMap.toSpanSingleton_apply, one_smul,
          CommSemiring.counit_apply] using g.isGroupLikeElem_val.counit_eq_one
      map_comp_comul := by
        apply LinearMap.ext_ring
        simpa only [LinearMap.comp_apply, CommSemiring.comul_apply, TensorProduct.map_tmul,
          LinearMap.toSpanSingleton_apply, one_smul]
          using g.isGroupLikeElem_val.comul_eq_tmul_self.symm }
  invFun f := ⟨f 1, IsGroupLikeElem.map f (isGroupLikeElem_self.mpr rfl)⟩
  left_inv g := by
    apply GroupLike.ext
    exact one_smul R g.val
  right_inv f := by
    apply CoalgHom.ext_of_ring
    exact one_smul R (f 1)

end GroupLike
end
