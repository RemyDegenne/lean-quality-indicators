public section

open Filter Function MeasureTheory Set Topology

open scoped ENNReal

open CKN CKN.Foundation.Parabolic

noncomputable section

namespace ESS

theorem vorticityFluxDeriv_sq_le {U : Fin 3 → Vec3 × ℝ → ℝ} {G Ω1 : Fin 3 → Fin 3 → Vec3 × ℝ → ℝ}
    {M : ℝ} {z : Vec3 × ℝ} (hz : ∀ i, |U i z| ≤ M) (i j m : Fin 3) :
    vorticityFluxDeriv U G Ω1 i j m z ^ 2 ≤
      16 * (∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2) ^ 2 +
        8 * M ^ 2 * ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2 := by
  set S := ∑ a : Fin 3, ∑ b : Fin 3, G a b z ^ 2 with hS
  set T := ∑ a : Fin 3, ∑ b : Fin 3, Ω1 a b z ^ 2 with hT
  have hGe : ∀ a b, G a b z ^ 2 ≤ S := fun a b =>
    (Finset.single_le_sum (f := fun b => G a b z ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, G a b z ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ a))
  have hΩe : ∀ a b, Ω1 a b z ^ 2 ≤ T := fun a b =>
    (Finset.single_le_sum (f := fun b => Ω1 a b z ^ 2) (fun _ _ => sq_nonneg _)
      (Finset.mem_univ b)).trans (Finset.single_le_sum (f := fun a => ∑ b : Fin 3, Ω1 a b z ^ 2)
        (fun _ _ => by positivity) (Finset.mem_univ a))
  have hw : ∀ l, vorticityCurl G l z ^ 2 ≤ 2 * S := fun l => vorticityCurl_sq_le G z l
  have hU2 : ∀ l, U l z ^ 2 ≤ M ^ 2 := fun l => by
    have := hz l
    have h0 : 0 ≤ |U l z| := abs_nonneg _
    nlinarith only [this, h0, sq_abs (U l z)]
  set A := G j m z * vorticityCurl G i z
  set B := U j z * Ω1 i m z
  set C := Ω1 j m z * U i z
  set D := vorticityCurl G j z * G i m z
  have hA : A ^ 2 ≤ 2 * S ^ 2 := by
    have h := mul_le_mul (hGe j m) (hw i) (sq_nonneg _) (by positivity)
    calc A ^ 2 = G j m z ^ 2 * vorticityCurl G i z ^ 2 := by ring
      _ ≤ S * (2 * S) := h
      _ = 2 * S ^ 2 := by ring
  have hB : B ^ 2 ≤ M ^ 2 * T := by
    have h := mul_le_mul (hU2 j) (hΩe i m) (sq_nonneg _) (sq_nonneg _)
    calc B ^ 2 = U j z ^ 2 * Ω1 i m z ^ 2 := by ring
      _ ≤ M ^ 2 * T := h
  have hC : C ^ 2 ≤ M ^ 2 * T := by
    have h := mul_le_mul (hU2 i) (hΩe j m) (sq_nonneg _) (sq_nonneg _)
    calc C ^ 2 = U i z ^ 2 * Ω1 j m z ^ 2 := by ring
      _ ≤ M ^ 2 * T := h
  have hD : D ^ 2 ≤ 2 * S ^ 2 := by
    have h := mul_le_mul (hw j) (hGe i m) (sq_nonneg _) (by positivity)
    calc D ^ 2 = vorticityCurl G j z ^ 2 * G i m z ^ 2 := by ring
      _ ≤ 2 * S * S := h
      _ = 2 * S ^ 2 := by ring
  have hsum : vorticityFluxDeriv U G Ω1 i j m z ^ 2 ≤ 4 * (A ^ 2 + B ^ 2 + C ^ 2 + D ^ 2) := by
    have e : vorticityFluxDeriv U G Ω1 i j m z = -((A + B) - (C + D)) := rfl
    rw [e]
    nlinarith only [sq_nonneg (A - B), sq_nonneg (A - C), sq_nonneg (A + D), sq_nonneg (B + C),
      sq_nonneg (B + D), sq_nonneg (C - D)]
  nlinarith only [hsum, hA, hB, hC, hD]

end ESS
end
end
