namespace OAI

noncomputable section

open scoped BigOperators Classical ComplexOrder MatrixOrder Matrix.Norms.L2Operator

open Matrix

namespace BinaryCoordinateSweeps.Density

variable {I : Type*} [Fintype I] [DecidableEq I]

omit [DecidableEq I] in
lemma compress_whitening_cap (P Q C : Matrix I I ℂ) (d : ℂ)
    (hQ : Q.IsHermitian) (hQQ : Q*Q=Q) (hPQ : P*Q=Q*P) (hCQ : C*Q=Q*C)
    (hc : (C*C-d•P).PosSemidef) : (C*Q*C-d•(Q*P)).PosSemidef := by
  have h := hc.mul_mul_conjTranspose_same Q
  rw [hQ.eq,Matrix.mul_sub,Matrix.sub_mul,Matrix.mul_smul,Matrix.smul_mul] at h
  have he1 : Q*(C*C)*Q = C*Q*C := by
    calc
      _ = (Q*C)*(C*Q) := by noncomm_ring
      _ = (C*Q)*(Q*C) := by rw [hCQ,← hCQ]
      _ = C*(Q*Q)*C := by noncomm_ring
      _ = _ := by rw [hQQ]
  have he2 : Q*P*Q = Q*P := by rw [mul_assoc,hPQ,← mul_assoc,hQQ]
  rwa [he1,he2] at h

end BinaryCoordinateSweeps.Density
end
end OAI
