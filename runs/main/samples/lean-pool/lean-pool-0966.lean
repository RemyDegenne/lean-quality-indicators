@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace MovingSofa

open MeasureTheory

open GerverAreaCert

theorem gerverOuterCap_area_certified_lower_bound :
    (28609 : ℝ) / 10000 ≤ ClassicalResults.area gerverOuterCap := by
  have hNN : NN = 64 := rfl
  have hTpos : (0 : ℝ) < Real.pi / 2 := by positivity
  have hcount : fanCount = 640 := rfl
  -- The fan data on `Fin 640`.
  have hlt : ∀ i : Fin 640, (i : ℕ) < fanCount := fun i => by
    rw [hcount]; exact i.isLt
  have hmono : StrictMono fun i : Fin 640 => gerverFanNormal (i : ℕ) := by
    refine Fin.strictMono_iff_lt_succ.2 fun i => ?_
    simpa using gerverFanNormal_lt_succ (i : ℕ) (by rw [hcount]; omega)
  obtain ⟨-, hfan⟩ := supportContact_fan_area gerverOuterCap
    isCompact_gerverOuterCap convex_gerverOuterCap gerverFanAnchor
    (gerver_outer_contact_C (Real.pi / 2) ⟨hTpos.le, le_rfl⟩)
    gerverFanAnchor_snd (fun _ hq => gerverOuterCap_quadrant hq) 639
    (fun i : Fin 640 => gerverFanNormal (i : ℕ)) hmono
    (fun i => gerverFanNormal_mem_Ico (i : ℕ) (hlt i))
    (fun i : Fin 640 => gerverFanPoint (i : ℕ)) (fun i => gerverFanPoint_mem (i : ℕ) (hlt i))
    (fun i q hq => gerverFanPoint_support (i : ℕ) (hlt i) hq)
  -- Identify the `Fin`-indexed fan sum with the certificate's range sum.
  rw [show (∑ i : Fin 639, planeCrossProduct
        (gerverFanPoint (i.castSucc : Fin 640) - gerverFanAnchor)
        (gerverFanPoint (i.succ : Fin 640) - gerverFanAnchor)) =
      ∑ i ∈ Finset.range (fanCount - 1),
        planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
          (gerverFanPoint (i + 1) - gerverFanAnchor) by
    rw [hcount]
    exact Fin.sum_univ_eq_sum_range (fun i => planeCrossProduct
      (gerverFanPoint i - gerverFanAnchor) (gerverFanPoint (i + 1) - gerverFanAnchor)) 639] at hfan
  -- The kernel-checked numeric inequality.  The fan sum and the certificate endpoint are
  -- abstracted into local variables first, and the arithmetic tactics are used in their
  -- `only` form, so that no tactic ever tries to evaluate the 639-term fold.
  obtain ⟨S, hS⟩ : ∃ S : ℝ, (∑ i ∈ Finset.range (fanCount - 1),
      planeCrossProduct (gerverFanPoint i - gerverFanAnchor)
        (gerverFanPoint (i + 1) - gerverFanAnchor)) = S := ⟨_, rfl⟩
  obtain ⟨z, hz⟩ : ∃ z : ℤ, capDoubledZ.lo = z := ⟨_, rfl⟩
  obtain ⟨hlo, -⟩ := capDoubledZ_sound
  rw [hS] at hfan
  rw [hS, hz] at hlo
  have hOK : 2 * 28609 * M ≤ 10000 * capDoubledZ.lo := by
    have h := capOK_true
    unfold capOK at h
    exact of_decide_eq_true h
  rw [hz] at hOK
  have hOK' : (2 * 28609 * (M : ℝ)) ≤ 10000 * (z : ℝ) := by exact_mod_cast hOK
  have hM : (0 : ℝ) < (M : ℝ) := SI.Mpos
  have hkey : 2 * 28609 ≤ 10000 * S := by nlinarith only [hlo, hOK', hM]
  refine le_trans ?_ hfan
  linarith only [hkey]

end MovingSofa
end
end
end
end
end
end
end
end
