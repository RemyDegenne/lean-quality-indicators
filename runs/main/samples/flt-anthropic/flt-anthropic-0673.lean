namespace M4aHerbrand.ArchSemilocal

open NumberField NumberField.InfinitePlace TensorProduct

open scoped NumberField.LiesOver

noncomputable section

variable {K L : Type*} [Field K] [NumberField K] [Field L] [NumberField L] [Algebra K L]

attribute [local instance] extLiesOver

theorem finrank_pi_extension (v : InfinitePlace K) :
    Module.finrank v.Completion ((w : v.Extension L) → w.1.Completion)
      = Module.finrank K L := by
  classical
  haveI : ∀ w : v.Extension L, FiniteDimensional v.Completion w.1.Completion :=
    fun w => finiteDimensional_completion v w.1
  haveI : ∀ w : v.Extension L, Module.Free v.Completion w.1.Completion :=
    fun w => Module.Free.of_divisionRing _ _
  rw [Module.finrank_pi_fintype v.Completion]
  rw [← sum_inertiaDeg_eq_finrank K L v]
  rw [← Finset.sum_coe_sort ((placesOver L v).toFinset) (fun w => v.inertiaDeg w)]
  let E : v.Extension L ≃ {w : InfinitePlace L // w ∈ (placesOver L v).toFinset} :=
    { toFun := fun w =>
        ⟨w.1, Set.mem_toFinset.mpr
          (show (w.1 : InfinitePlace L) ∈ placesOver L v from extLiesOver v w)⟩
      invFun := fun w =>
        have hmem : (w.1 : InfinitePlace L) ∈ placesOver L v := Set.mem_toFinset.mp w.2
        haveI : w.1.1.LiesOver v.1 := hmem
        ⟨w.1, LiesOver.comap_eq w.1 v⟩
      left_inv := fun w => Subtype.ext rfl
      right_inv := fun w => Subtype.ext rfl }
  exact Fintype.sum_equiv E _ _ (fun w => (inertiaDeg_eq_finrank v w.1).symm)

end
end M4aHerbrand.ArchSemilocal
