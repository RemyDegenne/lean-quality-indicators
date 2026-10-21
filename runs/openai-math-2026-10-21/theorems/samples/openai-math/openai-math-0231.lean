namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq1969 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm1969 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 1) (sourceB1969 + difference 1 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 1) (sourceB1969 + difference 1 0) sourceC1969) = raw27951 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27951; decide +kernel
    rw [ha]
    exact (canonical27951 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 2) (sourceB1969 + difference 2 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5047) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 2) (sourceB1969 + difference 2 0) sourceC1969) = raw27952 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27952; decide +kernel
    rw [ha]
    exact (canonical27952 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 3) (sourceB1969 + difference 3 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5107) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 3) (sourceB1969 + difference 3 0) sourceC1969) = raw27641 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27641; decide +kernel
    rw [ha]
    exact (canonical27641 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 4) (sourceB1969 + difference 4 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5000) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 4) (sourceB1969 + difference 4 0) sourceC1969) = raw27953 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27953; decide +kernel
    rw [ha]
    exact (canonical27953 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA1969 + difference 0 5) (sourceB1969 + difference 5 0) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4741) := by
    have ha : (tripleCharges (sourceA1969 + difference 0 5) (sourceB1969 + difference 5 0) sourceC1969) = raw27954 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27954; decide +kernel
    rw [ha]
    exact (canonical27954 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 0) (sourceB1969 + difference 0 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4853) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 0) (sourceB1969 + difference 0 1) sourceC1969) = raw27955 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27955; decide +kernel
    rw [ha]
    exact (canonical27955 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 2) (sourceB1969 + difference 2 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5048) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 2) (sourceB1969 + difference 2 1) sourceC1969) = raw27956 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27956; decide +kernel
    rw [ha]
    exact (canonical27956 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 3) (sourceB1969 + difference 3 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5109) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 3) (sourceB1969 + difference 3 1) sourceC1969) = raw27646 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27646; decide +kernel
    rw [ha]
    exact (canonical27646 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 4) (sourceB1969 + difference 4 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5001) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 4) (sourceB1969 + difference 4 1) sourceC1969) = raw27957 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27957; decide +kernel
    rw [ha]
    exact (canonical27957 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA1969 + difference 1 5) (sourceB1969 + difference 5 1) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4742) := by
    have ha : (tripleCharges (sourceA1969 + difference 1 5) (sourceB1969 + difference 5 1) sourceC1969) = raw27958 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27958; decide +kernel
    rw [ha]
    exact (canonical27958 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 0) (sourceB1969 + difference 0 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4792) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 0) (sourceB1969 + difference 0 2) sourceC1969) = raw27959 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27959; decide +kernel
    rw [ha]
    exact (canonical27959 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 1) (sourceB1969 + difference 1 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5065) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 1) (sourceB1969 + difference 1 2) sourceC1969) = raw27960 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27960; decide +kernel
    rw [ha]
    exact (canonical27960 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 3) (sourceB1969 + difference 3 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 3) (sourceB1969 + difference 3 2) sourceC1969) = raw27651 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27651; decide +kernel
    rw [ha]
    exact (canonical27651 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 4) (sourceB1969 + difference 4 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4992) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 4) (sourceB1969 + difference 4 2) sourceC1969) = raw27961 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27961; decide +kernel
    rw [ha]
    exact (canonical27961 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA1969 + difference 2 5) (sourceB1969 + difference 5 2) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4729) := by
    have ha : (tripleCharges (sourceA1969 + difference 2 5) (sourceB1969 + difference 5 2) sourceC1969) = raw27962 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27962; decide +kernel
    rw [ha]
    exact (canonical27962 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 0) (sourceB1969 + difference 0 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4817) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 0) (sourceB1969 + difference 0 3) sourceC1969) = raw27963 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27963; decide +kernel
    rw [ha]
    exact (canonical27963 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 1) (sourceB1969 + difference 1 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5087) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 1) (sourceB1969 + difference 1 3) sourceC1969) = raw27964 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27964; decide +kernel
    rw [ha]
    exact (canonical27964 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 2) (sourceB1969 + difference 2 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5052) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 2) (sourceB1969 + difference 2 3) sourceC1969) = raw27965 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27965; decide +kernel
    rw [ha]
    exact (canonical27965 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 4) (sourceB1969 + difference 4 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5008) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 4) (sourceB1969 + difference 4 3) sourceC1969) = raw27966 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27966; decide +kernel
    rw [ha]
    exact (canonical27966 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA1969 + difference 3 5) (sourceB1969 + difference 5 3) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4747) := by
    have ha : (tripleCharges (sourceA1969 + difference 3 5) (sourceB1969 + difference 5 3) sourceC1969) = raw27967 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27967; decide +kernel
    rw [ha]
    exact (canonical27967 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 0) (sourceB1969 + difference 0 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 0) (sourceB1969 + difference 0 4) sourceC1969) = raw27653 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27653; decide +kernel
    rw [ha]
    exact (canonical27653 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 1) (sourceB1969 + difference 1 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 1) (sourceB1969 + difference 1 4) sourceC1969) = raw27654 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27654; decide +kernel
    rw [ha]
    exact (canonical27654 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 2) (sourceB1969 + difference 2 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5128) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 2) (sourceB1969 + difference 2 4) sourceC1969) = raw27655 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27655; decide +kernel
    rw [ha]
    exact (canonical27655 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 3) (sourceB1969 + difference 3 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 3) (sourceB1969 + difference 3 4) sourceC1969) = raw27780 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27780; decide +kernel
    rw [ha]
    exact (canonical27780 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA1969 + difference 4 5) (sourceB1969 + difference 5 4) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4807) := by
    have ha : (tripleCharges (sourceA1969 + difference 4 5) (sourceB1969 + difference 5 4) sourceC1969) = raw27657 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27657; decide +kernel
    rw [ha]
    exact (canonical27657 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 0) (sourceB1969 + difference 0 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4804) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 0) (sourceB1969 + difference 0 5) sourceC1969) = raw27968 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27968; decide +kernel
    rw [ha]
    exact (canonical27968 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 1) (sourceB1969 + difference 1 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5075) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 1) (sourceB1969 + difference 1 5) sourceC1969) = raw27969 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27969; decide +kernel
    rw [ha]
    exact (canonical27969 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 2) (sourceB1969 + difference 2 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5127) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 2) (sourceB1969 + difference 2 5) sourceC1969) = raw27970 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27970; decide +kernel
    rw [ha]
    exact (canonical27970 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 3) (sourceB1969 + difference 3 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5171) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 3) (sourceB1969 + difference 3 5) sourceC1969) = raw27667 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27667; decide +kernel
    rw [ha]
    exact (canonical27667 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA1969 + difference 5 4) (sourceB1969 + difference 4 5) sourceC1969) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5147) := by
    have ha : (tripleCharges (sourceA1969 + difference 5 4) (sourceB1969 + difference 4 5) sourceC1969) = raw27971 := by
      apply Matrix.ext; unfold tripleCharges sourceA1969 sourceB1969 sourceC1969 difference raw27971; decide +kernel
    rw [ha]
    exact (canonical27971 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA1969 sourceB1969 sourceC1969
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm1969, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics
end OAI
