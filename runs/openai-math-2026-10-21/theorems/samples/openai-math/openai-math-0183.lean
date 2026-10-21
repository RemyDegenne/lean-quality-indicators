namespace OAI

noncomputable section

namespace KadisonSimilarity

namespace TracialCornerGeometry

universe u v

variable {P : Type u} [CStarAlgebra P]
  {H : Type v} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  (G : TracialCornerGeometry P H) (A D : StarSubalgebra ℂ P)
  [IsClosed (A : Set P)] [IsClosed (D : Set P)]
  {I : ℕ → Type*} [∀ j, Fintype (I j)] [∀ j, DecidableEq (I j)]
  [∀ j, Nonempty (I j)]
  (M : NestedTracialMatrices (A := I) (G.baseGeometry D).trace (G.baseGeometry D).vector)
  {b : ℝ} (Q : SmallFreeCornerData (G.baseGeometry D).trace b)
  (s : A) (hsstar : star s = s) (hssq : s * s = 1)

local notation "d" => Q.half.reflection

local notation "dU" => symmetryUnit (d : P)
  (congrArg (fun x : D => (x : P)) Q.half.reflection_square)

local notation "p" => dihedralHalfProjection dU

local notation "hp" => symmetryHalfProjectionProof d Q.half.reflection_star
  Q.half.reflection_square

local notation "C" => G.generatedDihedralAlgebra (d : P) (s : P)

local notation "K" => StarSubalgebra.topologicalClosure (factorAlgebra
  (CStarCorner.subalgebra p hp D
    (symmetryHalfProjection_mem D d Q.half.reflection_square Q.half.reflection.property))
  (CStarCorner.subalgebra p hp C
    (symmetryHalfProjection_mem C d Q.half.reflection_square
      (G.first_mem_generatedDihedralAlgebra (d : P) (s : P)))))

local instance smallFrameCorner_isClosed : IsClosed (K : Set (CStarCorner p hp)) :=
  StarSubalgebra.isClosed_topologicalClosure _

omit [IsClosed (A : Set P)] in
theorem smallFrameCompressionInput_proved (hτ : G.trace 1 = 1) :
    G.smallFrameCompressionInput A D Q s hτ := by
  unfold smallFrameCompressionInput
  exact ricardXuCompressionInput _ _ _

end TracialCornerGeometry
end KadisonSimilarity
end
end OAI
