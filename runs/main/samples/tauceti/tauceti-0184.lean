public section

open scoped TensorProduct

open TauCeti TauCeti.DiagonalizableGroup

namespace BialgHom

noncomputable section

variable {R H X V A : Type*} [CommSemiring R] [Semiring H] [Bialgebra R H]
  [CommMonoid X] [AddCommMonoid V] [Module R V] [Comodule R H V]
  [CommSemiring A] [Algebra R A]

theorem endOfPoint_comp_eq_of_eqOn_weights
    (π : H →ₐc[R] MonoidAlgebra R X) (f g : MonoidAlgebra R X →ₐ[R] A)
    (hfg : ∀ x, weightSpace V π.toCoalgHom x ≠ ⊥ →
      f (MonoidAlgebra.single x 1) = g (MonoidAlgebra.single x 1)) :
    Comodule.endOfPoint V (f.comp π.toAlgHom) =
      Comodule.endOfPoint V (g.comp π.toAlgHom) := by
  classical
  apply LinearMap.ext
  intro z
  induction z using TensorProduct.inductionOn with
  | add z t hz ht => simp [hz, ht]
  | tmul a v =>
      have hv : v ∈ ⨆ x, weightSpace V π.toCoalgHom x := by
        rw [(isInternal_weightSpace V π.toCoalgHom).submodule_iSup_eq_top]
        trivial
      refine Submodule.iSup_induction (weightSpace V π.toCoalgHom)
        (motive := fun v ↦ Comodule.endOfPoint V (f.comp π.toAlgHom) (a ⊗ₜ[R] v) =
          Comodule.endOfPoint V (g.comp π.toAlgHom) (a ⊗ₜ[R] v)) hv
        (fun x v hv ↦ ?_) (by simp) (fun v w hv hw ↦ ?_)
      · by_cases hx : weightSpace V π.toCoalgHom x = ⊥
        · have hv0 : v = 0 := by simpa [hx] using hv
          simp [hv0]
        · rw [endOfPoint_tmul_of_mem_weightSpace V π f a hv,
            endOfPoint_tmul_of_mem_weightSpace V π g a hv, hfg x hx]
      · simp [TensorProduct.tmul_add, hv, hw]

end
end BialgHom
end
