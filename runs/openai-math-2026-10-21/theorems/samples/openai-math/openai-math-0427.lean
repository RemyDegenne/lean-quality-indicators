namespace OAI

namespace MUB6.Certificate.MixedSemantics

open scoped BigOperators

theorem sourceEq435 (B : Fin 7 → Basis) (hB : IsMUBFamily B) :
    Integer.Sparse.eval sourceForm435 (mixedVector B) = 0 := by
  have hm0 : mixedMoment B (tripleCharges (sourceA435 + difference 0 1) (sourceB435 + difference 1 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA435 + difference 0 1) (sourceB435 + difference 1 0) sourceC435) = raw8002 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8002; decide +kernel
    rw [ha]
    exact (canonical8002 B hB).trans rfl
  have hm1 : mixedMoment B (tripleCharges (sourceA435 + difference 0 2) (sourceB435 + difference 2 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5434) := by
    have ha : (tripleCharges (sourceA435 + difference 0 2) (sourceB435 + difference 2 0) sourceC435) = raw8003 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8003; decide +kernel
    rw [ha]
    exact (canonical8003 B hB).trans rfl
  have hm2 : mixedMoment B (tripleCharges (sourceA435 + difference 0 3) (sourceB435 + difference 3 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5442) := by
    have ha : (tripleCharges (sourceA435 + difference 0 3) (sourceB435 + difference 3 0) sourceC435) = raw8004 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8004; decide +kernel
    rw [ha]
    exact (canonical8004 B hB).trans rfl
  have hm3 : mixedMoment B (tripleCharges (sourceA435 + difference 0 4) (sourceB435 + difference 4 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5455) := by
    have ha : (tripleCharges (sourceA435 + difference 0 4) (sourceB435 + difference 4 0) sourceC435) = raw8005 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8005; decide +kernel
    rw [ha]
    exact (canonical8005 B hB).trans rfl
  have hm4 : mixedMoment B (tripleCharges (sourceA435 + difference 0 5) (sourceB435 + difference 5 0) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5492) := by
    have ha : (tripleCharges (sourceA435 + difference 0 5) (sourceB435 + difference 5 0) sourceC435) = raw8006 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8006; decide +kernel
    rw [ha]
    exact (canonical8006 B hB).trans rfl
  have hm5 : mixedMoment B (tripleCharges (sourceA435 + difference 1 0) (sourceB435 + difference 0 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA435 + difference 1 0) (sourceB435 + difference 0 1) sourceC435) = raw8007 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8007; decide +kernel
    rw [ha]
    exact (canonical8007 B hB).trans rfl
  have hm6 : mixedMoment B (tripleCharges (sourceA435 + difference 1 2) (sourceB435 + difference 2 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA435 + difference 1 2) (sourceB435 + difference 2 1) sourceC435) = raw8008 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8008; decide +kernel
    rw [ha]
    exact (canonical8008 B hB).trans rfl
  have hm7 : mixedMoment B (tripleCharges (sourceA435 + difference 1 3) (sourceB435 + difference 3 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA435 + difference 1 3) (sourceB435 + difference 3 1) sourceC435) = raw8009 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8009; decide +kernel
    rw [ha]
    exact (canonical8009 B hB).trans rfl
  have hm8 : mixedMoment B (tripleCharges (sourceA435 + difference 1 4) (sourceB435 + difference 4 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA435 + difference 1 4) (sourceB435 + difference 4 1) sourceC435) = raw8010 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8010; decide +kernel
    rw [ha]
    exact (canonical8010 B hB).trans rfl
  have hm9 : mixedMoment B (tripleCharges (sourceA435 + difference 1 5) (sourceB435 + difference 5 1) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA435 + difference 1 5) (sourceB435 + difference 5 1) sourceC435) = raw8011 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8011; decide +kernel
    rw [ha]
    exact (canonical8011 B hB).trans rfl
  have hm10 : mixedMoment B (tripleCharges (sourceA435 + difference 2 0) (sourceB435 + difference 0 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4461) := by
    have ha : (tripleCharges (sourceA435 + difference 2 0) (sourceB435 + difference 0 2) sourceC435) = raw8012 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8012; decide +kernel
    rw [ha]
    exact (canonical8012 B hB).trans rfl
  have hm11 : mixedMoment B (tripleCharges (sourceA435 + difference 2 1) (sourceB435 + difference 1 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5076) := by
    have ha : (tripleCharges (sourceA435 + difference 2 1) (sourceB435 + difference 1 2) sourceC435) = raw8013 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8013; decide +kernel
    rw [ha]
    exact (canonical8013 B hB).trans rfl
  have hm12 : mixedMoment B (tripleCharges (sourceA435 + difference 2 3) (sourceB435 + difference 3 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5172) := by
    have ha : (tripleCharges (sourceA435 + difference 2 3) (sourceB435 + difference 3 2) sourceC435) = raw8014 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8014; decide +kernel
    rw [ha]
    exact (canonical8014 B hB).trans rfl
  have hm13 : mixedMoment B (tripleCharges (sourceA435 + difference 2 4) (sourceB435 + difference 4 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5294) := by
    have ha : (tripleCharges (sourceA435 + difference 2 4) (sourceB435 + difference 4 2) sourceC435) = raw8015 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8015; decide +kernel
    rw [ha]
    exact (canonical8015 B hB).trans rfl
  have hm14 : mixedMoment B (tripleCharges (sourceA435 + difference 2 5) (sourceB435 + difference 5 2) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5290) := by
    have ha : (tripleCharges (sourceA435 + difference 2 5) (sourceB435 + difference 5 2) sourceC435) = raw8016 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8016; decide +kernel
    rw [ha]
    exact (canonical8016 B hB).trans rfl
  have hm15 : mixedMoment B (tripleCharges (sourceA435 + difference 3 0) (sourceB435 + difference 0 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4503) := by
    have ha : (tripleCharges (sourceA435 + difference 3 0) (sourceB435 + difference 0 3) sourceC435) = raw8017 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8017; decide +kernel
    rw [ha]
    exact (canonical8017 B hB).trans rfl
  have hm16 : mixedMoment B (tripleCharges (sourceA435 + difference 3 1) (sourceB435 + difference 1 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA435 + difference 3 1) (sourceB435 + difference 1 3) sourceC435) = raw8018 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8018; decide +kernel
    rw [ha]
    exact (canonical8018 B hB).trans rfl
  have hm17 : mixedMoment B (tripleCharges (sourceA435 + difference 3 2) (sourceB435 + difference 2 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5105) := by
    have ha : (tripleCharges (sourceA435 + difference 3 2) (sourceB435 + difference 2 3) sourceC435) = raw8019 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8019; decide +kernel
    rw [ha]
    exact (canonical8019 B hB).trans rfl
  have hm18 : mixedMoment B (tripleCharges (sourceA435 + difference 3 4) (sourceB435 + difference 4 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5310) := by
    have ha : (tripleCharges (sourceA435 + difference 3 4) (sourceB435 + difference 4 3) sourceC435) = raw8020 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8020; decide +kernel
    rw [ha]
    exact (canonical8020 B hB).trans rfl
  have hm19 : mixedMoment B (tripleCharges (sourceA435 + difference 3 5) (sourceB435 + difference 5 3) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5304) := by
    have ha : (tripleCharges (sourceA435 + difference 3 5) (sourceB435 + difference 5 3) sourceC435) = raw8021 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8021; decide +kernel
    rw [ha]
    exact (canonical8021 B hB).trans rfl
  have hm20 : mixedMoment B (tripleCharges (sourceA435 + difference 4 0) (sourceB435 + difference 0 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4466) := by
    have ha : (tripleCharges (sourceA435 + difference 4 0) (sourceB435 + difference 0 4) sourceC435) = raw8022 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8022; decide +kernel
    rw [ha]
    exact (canonical8022 B hB).trans rfl
  have hm21 : mixedMoment B (tripleCharges (sourceA435 + difference 4 1) (sourceB435 + difference 1 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA435 + difference 4 1) (sourceB435 + difference 1 4) sourceC435) = raw8023 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8023; decide +kernel
    rw [ha]
    exact (canonical8023 B hB).trans rfl
  have hm22 : mixedMoment B (tripleCharges (sourceA435 + difference 4 2) (sourceB435 + difference 2 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5080) := by
    have ha : (tripleCharges (sourceA435 + difference 4 2) (sourceB435 + difference 2 4) sourceC435) = raw8024 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8024; decide +kernel
    rw [ha]
    exact (canonical8024 B hB).trans rfl
  have hm23 : mixedMoment B (tripleCharges (sourceA435 + difference 4 3) (sourceB435 + difference 3 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5176) := by
    have ha : (tripleCharges (sourceA435 + difference 4 3) (sourceB435 + difference 3 4) sourceC435) = raw8025 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8025; decide +kernel
    rw [ha]
    exact (canonical8025 B hB).trans rfl
  have hm24 : mixedMoment B (tripleCharges (sourceA435 + difference 4 5) (sourceB435 + difference 5 4) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5291) := by
    have ha : (tripleCharges (sourceA435 + difference 4 5) (sourceB435 + difference 5 4) sourceC435) = raw8026 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8026; decide +kernel
    rw [ha]
    exact (canonical8026 B hB).trans rfl
  have hm25 : mixedMoment B (tripleCharges (sourceA435 + difference 5 0) (sourceB435 + difference 0 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 4463) := by
    have ha : (tripleCharges (sourceA435 + difference 5 0) (sourceB435 + difference 0 5) sourceC435) = raw8027 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8027; decide +kernel
    rw [ha]
    exact (canonical8027 B hB).trans rfl
  have hm26 : mixedMoment B (tripleCharges (sourceA435 + difference 5 1) (sourceB435 + difference 1 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA435 + difference 5 1) (sourceB435 + difference 1 5) sourceC435) = raw8028 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8028; decide +kernel
    rw [ha]
    exact (canonical8028 B hB).trans rfl
  have hm27 : mixedMoment B (tripleCharges (sourceA435 + difference 5 2) (sourceB435 + difference 2 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5078) := by
    have ha : (tripleCharges (sourceA435 + difference 5 2) (sourceB435 + difference 2 5) sourceC435) = raw8029 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8029; decide +kernel
    rw [ha]
    exact (canonical8029 B hB).trans rfl
  have hm28 : mixedMoment B (tripleCharges (sourceA435 + difference 5 3) (sourceB435 + difference 3 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5174) := by
    have ha : (tripleCharges (sourceA435 + difference 5 3) (sourceB435 + difference 3 5) sourceC435) = raw8030 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8030; decide +kernel
    rw [ha]
    exact (canonical8030 B hB).trans rfl
  have hm29 : mixedMoment B (tripleCharges (sourceA435 + difference 5 4) (sourceB435 + difference 4 5) sourceC435) (![0, 1, 2] : Fin 3 → Fin 3) =
      mixedVector B (Sum.inr 5296) := by
    have ha : (tripleCharges (sourceA435 + difference 5 4) (sourceB435 + difference 4 5) sourceC435) = raw8031 := by
      apply Matrix.ext; unfold tripleCharges sourceA435 sourceB435 sourceC435 difference raw8031; decide +kernel
    rw [ha]
    exact (canonical8031 B hB).trans rfl
  have hs := mixedMoment_different B hB sourceA435 sourceB435 sourceC435
    (0 : Fin 3) 1 2 (by decide)
  rw [offDiagSum_explicit] at hs
  rw [hm0, hm1, hm2, hm3, hm4, hm5, hm6, hm7, hm8, hm9, hm10, hm11, hm12, hm13, hm14, hm15, hm16, hm17, hm18, hm19, hm20, hm21, hm22, hm23, hm24, hm25, hm26, hm27, hm28, hm29] at hs
  norm_num [sourceForm435, Integer.Sparse.eval]
  linarith only [hs]

end MUB6.Certificate.MixedSemantics
end OAI
