namespace OAI

noncomputable section

open Set

namespace MarkovSuperreflexivity

universe u

variable {X : Type u} [AddCommGroup X] [Module ℝ X]

variable {Y : Type u} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem PowerSmooth.uniformSmooth {p : Seminorm ℝ Y} {q C : ℝ}
    (h : PowerSmooth p q C) (hq : 1 < q) (hC : 0 ≤ C) : UniformSmooth p := by
  intro ε hε
  have hCpos : 0 < C + 1 := by linarith
  have hrpos : 0 < q - 1 := sub_pos.mpr hq
  have hbase : 0 < ε / (C + 1) := div_pos hε hCpos
  let δ : ℝ := (ε / (C + 1)) ^ (q - 1)⁻¹
  have hδ : 0 < δ := Real.rpow_pos_of_pos hbase _
  refine ⟨δ, hδ, ?_⟩
  intro t ht htd x y hx hy
  have hpower : t ^ (q - 1) < ε / (C + 1) := by
    have htq := Real.rpow_lt_rpow ht.le htd hrpos
    simpa only [δ, Real.rpow_inv_rpow hbase.le hrpos.ne'] using htq
  have hscaled : t ^ (q - 1) * (C + 1) < ε :=
    (lt_div_iff₀ hCpos).mp hpower
  have hpnonneg := Real.rpow_nonneg ht.le (q - 1)
  have hfactor : C * t ^ (q - 1) ≤ ε := by nlinarith
  have hsplit : t ^ q = t ^ (q - 1) * t := by
    calc
      t ^ q = t ^ ((q - 1) + 1) := by congr 1 ; ring
      _ = t ^ (q - 1) * t ^ (1 : ℝ) := Real.rpow_add ht _ _
      _ = t ^ (q - 1) * t := by rw [Real.rpow_one]
  have hbound : C * t ^ q ≤ ε * t := by
    rw [hsplit, ← mul_assoc]
    exact mul_le_mul_of_nonneg_right hfactor ht.le
  exact (h x y hx hy t ht.le).trans (add_le_add (le_refl (1 : ℝ)) hbound)

end MarkovSuperreflexivity
end
end OAI
