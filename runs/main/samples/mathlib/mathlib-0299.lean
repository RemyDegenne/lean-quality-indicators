@[expose] public section

variable {R : Type*} [CommRing R] (I : Ideal R)

variable {M : Type*} [AddCommGroup M] [Module R M]

variable {N : Type*} [AddCommGroup N] [Module R N]

variable {P : Type*} [AddCommGroup P] [Module R P]

variable {T : Type*} [AddCommGroup T] [Module (AdicCompletion I R) T]

namespace AdicCompletion

open LinearMap

section Families

variable {ι : Type*} (M : ι → Type*) [∀ i, AddCommGroup (M i)]
  [∀ i, Module R (M i)]

section Sum

open DirectSum

variable [Fintype ι]

variable [DecidableEq ι]

theorem sum_comp_sumInv : sum I M ∘ₗ sumInv I M = LinearMap.id := by
  ext f n
  simp only [LinearMap.coe_comp, Function.comp_apply, LinearMap.id_coe, id_eq, mk_apply_coe,
    Submodule.mkQ_apply]
  rw [← DirectSum.sum_univ_of (((sumInv I M) ((AdicCompletion.mk I (⨁ (j : ι), M j)) f)))]
  simp only [sumInv_apply, map_mk, map_sum, sum_of, val_sum_apply, mk_apply_coe,
    AdicCauchySequence.map_apply_coe]
  simp only [← Submodule.mkQ_apply, ← map_sum, ← apply_eq_component, lof_eq_of,
    DirectSum.sum_univ_of]

end Sum
end Families
end AdicCompletion
end
