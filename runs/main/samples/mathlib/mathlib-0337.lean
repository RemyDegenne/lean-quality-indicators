@[expose] public section

noncomputable section

open scoped Topology

open Filter (Tendsto)

open ContinuousLinearMap

section CommSemiring

variable {𝕜 A : Type*} [CommSemiring 𝕜] [SeminormedRing A] [Algebra 𝕜 A]

theorem isBoundedBilinearMap_smul {E : Type*} [SeminormedAddCommGroup E] [Module 𝕜 E]
    [Module A E] [IsBoundedSMul A E] [IsScalarTower 𝕜 A E] :
    IsBoundedBilinearMap 𝕜 fun p : A × E ↦ p.1 • p.2 where
  add_left := add_smul
  add_right := smul_add
  smul_left := smul_assoc
  smul_right c x := smul_comm x c
  bound := ⟨1, one_pos, fun x y ↦ by grw [one_mul, norm_smul_le]⟩

end CommSemiring
end
end
