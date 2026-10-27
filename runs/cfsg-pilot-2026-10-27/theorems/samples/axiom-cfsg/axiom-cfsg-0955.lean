public section

namespace CFSG.LinearAlgebra

open Matrix

variable {K : Type*} [Field K] {n k : ℕ}

theorem exists_rref (V : Submodule K (Fin n → K)) (hV : Module.finrank K V = k) :
    ∃ H : Matrix (Fin k) (Fin n) K, H.IsReducedRowEchelon ∧
      Submodule.span K (Set.range H) = V := by
  classical
  set Lead : Finset (Fin n) :=
    Finset.univ.filter fun c => ∃ v ∈ V, (∀ j < c, v j = 0) ∧ v c ≠ 0 with hLeaddef
  have hLead : ∀ c, c ∈ Lead ↔ ∃ v ∈ V, (∀ j < c, v j = 0) ∧ v c ≠ 0 := fun c => by
    simp [hLeaddef]
  have hlead : ∀ v ∈ V, v ≠ 0 → ∃ c ∈ Lead, (∀ j < c, v j = 0) ∧ v c ≠ 0 := by
    intro v hv hv0
    obtain ⟨c, hc, hmin⟩ := WellFounded.has_min wellFounded_lt {j | v j ≠ 0}
      (Function.ne_iff.mp hv0)
    have h1 : ∀ j < c, v j = 0 := fun j hj => by
      by_contra h
      exact hmin j h hj
    exact ⟨c, (hLead c).mpr ⟨v, hv, h1, hc⟩, h1, hc⟩
  have hinj : ∀ v ∈ V, (∀ c : Lead, v c = 0) → v = 0 := by
    intro v hv h0
    by_contra hv0
    obtain ⟨c, hc, -, hvc⟩ := hlead v hv hv0
    exact hvc (h0 ⟨c, hc⟩)
  have hw : ∀ c : Lead, ∃ w ∈ V, (∀ j < (c : Fin n), w j = 0) ∧ w c ≠ 0 :=
    fun c => (hLead c).mp c.2
  choose w hwV hw0 hwc using hw
  set M : Matrix Lead Lead K := fun c c' => w c c' with hMdef
  have hMtri : M.IsUpperTriangular := fun c c' hlt => hw0 c c' hlt
  have hMdet : IsUnit M.det := by
    rw [det_of_isUpperTriangular hMtri]
    exact isUnit_iff_ne_zero.mpr (Finset.prod_ne_zero_iff.mpr fun c _ => hwc c)
  set u : Lead → Fin n → K := fun c₀ => ∑ c, M⁻¹ c₀ c • w c with hudef
  have huV : ∀ c₀, u c₀ ∈ V := fun c₀ =>
    Submodule.sum_mem _ fun c _ => Submodule.smul_mem _ _ (hwV c)
  have huδ : ∀ c₀ c' : Lead, u c₀ c' = (1 : Matrix Lead Lead K) c₀ c' := by
    intro c₀ c'
    rw [← nonsing_inv_mul M hMdet, Matrix.mul_apply]
    simp only [hudef, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rfl
  have hexp : ∀ v ∈ V, v = ∑ c : Lead, v c • u c := by
    intro v hv
    refine sub_eq_zero.mp (hinj _ (sub_mem hv (Submodule.sum_mem _ fun c _ =>
      Submodule.smul_mem _ _ (huV c))) fun c' => ?_)
    rw [Pi.sub_apply, Finset.sum_apply, sub_eq_zero, Finset.sum_eq_single c']
    · rw [Pi.smul_apply, smul_eq_mul, huδ, one_apply_eq, mul_one]
    · intro c _ hc
      rw [Pi.smul_apply, smul_eq_mul, huδ, one_apply_ne hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hli : LinearIndependent K u := by
    refine Fintype.linearIndependent_iff.mpr fun g hg c₀ => ?_
    have h1 := congrFun hg c₀
    rw [Finset.sum_apply, Finset.sum_eq_single c₀] at h1
    · rwa [Pi.smul_apply, smul_eq_mul, huδ, one_apply_eq, mul_one] at h1
    · intro c _ hc
      rw [Pi.smul_apply, smul_eq_mul, huδ, one_apply_ne hc, mul_zero]
    · intro h
      exact absurd (Finset.mem_univ _) h
  have hspan : Submodule.span K (Set.range u) = V := by
    refine le_antisymm (Submodule.span_le.mpr ?_) fun v hv => ?_
    · rintro _ ⟨c, rfl⟩
      exact huV c
    · rw [hexp v hv]
      exact Submodule.sum_mem _ fun c _ =>
        Submodule.smul_mem _ _ (Submodule.subset_span ⟨c, rfl⟩)
  have hcard : Lead.card = k := by
    rw [← hV, ← hspan, finrank_span_eq_card hli, Fintype.card_coe]
  set e := Lead.orderIsoOfFin hcard with he
  have hLE : ∀ i : Fin k, (∀ j < ((e i : Lead) : Fin n), u (e i) j = 0) ∧
      u (e i) (e i) ≠ 0 := by
    intro i
    have h1 : u (e i) (e i) = 1 := by rw [huδ, one_apply_eq]
    have hne : u (e i) ≠ 0 := fun h0 => by
      rw [h0, Pi.zero_apply] at h1
      exact zero_ne_one h1
    obtain ⟨c, hc, hc0, hcne⟩ := hlead _ (huV (e i)) hne
    have hce : (⟨c, hc⟩ : Lead) = e i := by
      by_contra hne'
      apply hcne
      rw [show c = ((⟨c, hc⟩ : Lead) : Fin n) from rfl, huδ, one_apply_ne (Ne.symm hne')]
    have hce' : c = ((e i : Lead) : Fin n) := congrArg Subtype.val hce
    rw [← hce']
    exact ⟨hc0, hcne⟩
  set H : Matrix (Fin k) (Fin n) K := fun i => u (e i) with hHdef
  have hHlead : ∀ i, H.IsLeadingEntry i ((e i : Lead) : Fin n) := hLE
  have hHuniq : ∀ i c, H.IsLeadingEntry i c → c = ((e i : Lead) : Fin n) :=
    fun i c hc => IsLeadingEntry.unique hc (hHlead i)
  have hmono : StrictMono fun i => ((e i : Lead) : Fin n) := fun i₁ i₂ hlt => e.strictMono hlt
  refine ⟨H, ⟨fun i₁ i₂ hlt j₂ hz => ?_, fun i c hc => ?_, fun i₁ i₂ c hlt hc => ?_⟩, ?_⟩
  · have hj : j₂ ≤ ((e i₁ : Lead) : Fin n) := by
      by_contra hgt
      push Not at hgt
      exact (hHlead i₁).2 (hz _ hgt)
    exact (hHlead i₂).1 j₂ (lt_of_le_of_lt hj (hmono hlt))
  · rw [hHuniq i c hc]
    change u (e i) (e i) = 1
    rw [huδ, one_apply_eq]
  · rw [hHuniq i₂ c hc]
    change u (e i₁) (e i₂) = 0
    rw [huδ, one_apply_ne (e.injective.ne hlt.ne)]
  · rw [← hspan]
    refine le_antisymm (Submodule.span_le.mpr ?_) (Submodule.span_le.mpr ?_)
    · rintro _ ⟨i, rfl⟩
      exact Submodule.subset_span ⟨e i, rfl⟩
    · rintro _ ⟨c, rfl⟩
      exact Submodule.subset_span ⟨e.symm c, by simp [hHdef]⟩

end CFSG.LinearAlgebra
end
