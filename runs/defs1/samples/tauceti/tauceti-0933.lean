public section

namespace TauCeti

open CategoryTheory _root_.DirectSum

universe u w

variable (k : Type w) [Field k] {V : Type u} (G : SimpleGraph V) [Finite V]
  (hns : ∀ i : V, ∃ j, G.Adj i j)

local notation "Z" => nonisolatedZigzagQuotient k G

/-- Right multiplication by the volume descends from `P_i` to its graded head and raises
internal degree by two. -/
noncomputable def zigzagGradedHeadToSocle (i : V) :
    zigzagGradedSimple k G i ⟶ (zigzagGradedProjectiveSocle k G hns i).shiftObj (-2) :=
  let _ := zigzagIntegerGradedAlgebra k G
  eqToHom (zigzagGradedSimple_def k G i) ≫
    GradedModuleCat.ofHom
      (gradedPositiveMulQuotientLift (zigzagVertexIdempotent_mem_zigzagIntegerGrade_zero k G i)
        (zigzagGradedSocleVolume k G hns i) (positiveIdeal_smul_socleVolume k G hns i))
      (LinearMap.isHomogeneous_def.2 fun p y hy => by
        obtain ⟨x, hx, rfl⟩ := mem_gradedPositiveMulQuotient_piece_iff _ |>.1 hy
        rw [gradedPositiveMulQuotientLift_gradedPositiveMulQuotientMk,
          GradedModuleCat.mem_shiftObj_piece_iff]
        let _ := (zigzagGradedProjectiveSocle k G hns i).gradedSMul
        have hm := SetLike.GradedSMul.smul_mem
          (B := (zigzagGradedProjectiveSocle k G hns i).grading.piece) hx
          (zigzagGradedSocleVolume_mem_grade_two k G hns i)
        simpa only [vadd_eq_add, add_zero, sub_neg_eq_add] using hm)

end TauCeti
end
