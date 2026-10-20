@[expose] public section

noncomputable section

universe u v

namespace ValuationRing

variable {V : Type u} [CommRing V] [IsDomain V] [ValuationRing V]
  (S : Submonoid V) (Vₛ : Type v) [CommRing Vₛ] [Algebra V Vₛ] [IsLocalization S Vₛ]

theorem isHausdorff_localization_span_singleton {a : V}
    (hS : Disjoint (S : Set V) ((Ideal.span {a}).radical : Set V))
    [IsHausdorff (Ideal.span {a}) V] :
    IsHausdorff (Ideal.span {algebraMap V Vₛ a}) Vₛ := by
  have hS0 : (0 : V) ∉ S := by
    intro h0
    exact Set.disjoint_left.1 hS h0 (Ideal.zero_mem _)
  have hSnzd : S ≤ nonZeroDivisors V := le_nonZeroDivisors_of_noZeroDivisors hS0
  have hinj : Function.Injective (algebraMap V Vₛ) := IsLocalization.injective Vₛ hSnzd
  refine ⟨fun x hx ↦ ?_⟩
  have hxpow (n : ℕ) : x ∈ (Ideal.span {algebraMap V Vₛ a}) ^ n := by
    simpa only [SModEq.zero, smul_eq_mul, Ideal.mul_top] using hx n
  have hximage (n : ℕ) :
      x ∈ localizedPowerImage (V := V) (Vₛ := Vₛ) a n :=
    (localizedPowerImage_sandwich S Vₛ hS n).1 (hxpow (n + 1))
  obtain ⟨y, hy, hyx⟩ := hximage 0
  have hyall (n : ℕ) : y ∈ (Ideal.span {a}) ^ n := by
    obtain ⟨z, hz, hzx⟩ := hximage n
    have hzy : z = y := hinj (hzx.trans hyx.symm)
    exact hzy ▸ hz
  have hy0 : y = 0 := IsHausdorff.haus (inferInstance : IsHausdorff (Ideal.span {a}) V) y
    (fun n ↦ by
      rw [SModEq.zero]
      simpa only [smul_eq_mul, Ideal.mul_top] using hyall n)
  rw [← hyx, hy0, map_zero]

end ValuationRing
end
end
