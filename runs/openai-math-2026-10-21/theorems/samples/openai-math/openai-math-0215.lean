namespace OAI

universe uT uE uI uI2 uA uB

section

open scoped Classical

open Matrix

namespace StrongThinTree.MultiGraph.Hierarchy

noncomputable section

open Finset StrongThinTree.Geometry StrongThinTree.Geometry.RadialShell

open scoped Classical

variable {n m h : ℕ} {H : Hierarchy n} {G : MultiGraph n m}
  {X : Fin n → Fin h → ℝ}

lemma homogeneous_family (T : Finset (Finset (Fin n))) (F : Finset (Fin n) → Finset (Fin m))
    (Y : Fin n → EuclideanSpace ℝ (Fin m))
    (hTne : T.Nonempty) (hT : T ⊆ H.nodes) (hroot : ∀t ∈ T, t ≠ univ)
    (hF : ∀t ∈ T, F t ⊆ H.parentBoundary G t) (hFn : ∀t ∈ T, (F t).Nonempty)
    {α γ ε c₁ c₂ : ℝ} (hα : 0 < α) (hγ : 0 < γ)
    (he : 0 < ε) (he1 : ε < 1/3) (hc₁ : 0 < c₁) (hc₂ : 0 < c₂)
    (hcontract : ∀u v, ‖Y u-Y v‖^2 ≤ l1dist (X u) (X v))
    (hpositive : ∀e, 0 ≤ (Y (G.left e)-Y (G.right e)).ofLp e)
    (hmin : ∀t ∈ T, ∀e ∈ F t, c₁ ≤ ((Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hmax : ∀t ∈ T, ∀e ∈ F t, ((Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤ 4*c₁)
    (hdmin : ∀t ∈ T, ∀e ∈ F t, c₂/4 ≤ l1dist (X (G.left e)) (X (G.right e)))
    (hdmax : ∀t ∈ T, ∀e ∈ F t, l1dist (X (G.left e)) (X (G.right e)) ≤ c₂)
    (hbad : ∀t ∈ T, α*((H.parentBoundary G t).card : ℝ)*
      (∑e ∈ H.parentBoundary G t, l1dist (X (G.left e)) (X (G.right e))) ≤
      (∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hdom : ∀t ∈ T, γ*(∑e ∈ H.parentBoundary G t, (Y (G.left e)-Y (G.right e)).ofLp e)^2 ≤
      (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2)
    (hsmall : (α*γ/32)^ε ≤ 1/(1728*(1024/ε^2))) :
    let s := α*γ/32
    let R := ∑t ∈ T, (∑e ∈ F t, (Y (G.left e)-Y (G.right e)).ofLp e)^2/
      ((H.parentBoundary G t).card : ℝ)
    (∃δ Δ : ℝ, ∃B : CompactFamily X δ Δ,
      s*c₁ ≤ δ ∧ Δ ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ δ*(∑D ∈ B.bags, (D.card : ℝ))) ∨
    (∃B : AssignedFamily H G X (s^(1+2*ε)), B.owners ⊆ T ∧
      s*c₁ ≤ B.radius ∧ B.radius ≤ 12*c₁/s ∧ s^ε*R/(6912*(1024/ε^2)) ≤ B.mass) := by
  let a : Fin m → ℝ := fun e => (Y (G.left e)-Y (G.right e)).ofLp e
  let d : Fin m → ℝ := fun e => l1dist (X (G.left e)) (X (G.right e))
  let E := T.biUnion F
  let N : ℝ := ∑t ∈ T, ((H.parentBoundary G t).card : ℝ)
  let N' : ℝ := E.card
  let s := α*γ/32
  let C : ℝ := 1024/ε^2
  let R := ∑t ∈ T, (∑e ∈ F t, a e)^2/((H.parentBoundary G t).card : ℝ)
  have hs : 0 < s := by dsimp [s]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  have hEn : E.Nonempty := by
    obtain ⟨t,ht⟩ := hTne
    obtain ⟨e,he⟩ := hFn t ht
    exact ⟨e,mem_biUnion.mpr ⟨t,ht,he⟩⟩
  have hN' : 0 < N' := by dsimp [N']; exact_mod_cast card_pos.mpr hEn
  have hboundary : ∀t ∈ T, 0 < (H.parentBoundary G t).card :=
    fun t ht => card_pos.mpr ((hFn t ht).mono (hF t ht))
  have hN : 0 < N := by
    apply sum_pos (fun t ht => ?_) hTne
    exact_mod_cast hboundary t ht
  have hNle : N' ≤ N := by
    have h1 : E.card ≤ ∑t ∈ T, (F t).card := card_biUnion_le
    have h2 : (∑t ∈ T, (F t).card) ≤ ∑t ∈ T, (H.parentBoundary G t).card :=
      sum_le_sum (fun t ht => card_le_card (hF t ht))
    dsimp [N',N]
    exact_mod_cast h1.trans h2
  have hd0 : ∀e, 0 ≤ d e := fun e => l1dist_nonneg _ _
  obtain ⟨hdensity,hR⟩ := StrongThinTree.BagDensity.family_density T (H.parentBoundary G) F a d
    hα hγ hc₁.le hF hFn (fun t ht e he => hd0 e) hmax hdmin hbad hdom
    (H.subset_boundary_multiplicity G T hT hroot F hF)
  change s*N*c₂ ≤ c₁*N' at hdensity
  change R ≤ 8*c₁*N' at hR
  let specα := s*N/N'
  have ha0 : 0 < specα := div_pos (mul_pos hs hN) hN'
  have hscale : specα*N' = s*N := div_mul_cancel₀ _ hN'.ne'
  have has : s ≤ specα := by
    apply (le_div_iff₀ hN').mpr
    exact mul_le_mul_of_nonneg_left hNle hs.le
  have had : specα*c₂ ≤ c₁ := by
    change (s*N/N')*c₂ ≤ c₁
    rw [div_mul_eq_mul_div]
    exact (div_le_iff₀ hN').mpr hdensity
  have hminE : ∀e ∈ E, c₁ ≤ (a e)^2 := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hmin t ht e he
  have hmaxE : ∀e ∈ E, d e ≤ c₂ := by
    intro e he
    obtain ⟨t,ht,he⟩ := mem_biUnion.mp he
    exact hdmax t ht e he
  let u : E → Fin n := fun e => G.left e.val
  let v : E → Fin n := fun e => G.right e.val
  have hIE : Fintype.card E = E.card := Fintype.card_coe E
  have hI : 0 < Fintype.card E := by rw [hIE]; exact card_pos.mpr hEn
  have hbnd : specα*(Fintype.card E : ℝ)*(∑e : E, ‖Y (u e)-Y (v e)‖^2) ≤
      (∑e : E, (Y (u e)-Y (v e)).ofLp e.val)^2 :=
    density_spectral_input (fun e : E => a e.val) (fun e : E => ‖Y (u e)-Y (v e)‖^2)
      hc₁.le ha0.le (fun e => hpositive e.val) (fun e => hminE e.val e.property)
      (fun e => (hcontract (u e) (v e)).trans (hmaxE e.val e.property)) had
  obtain ⟨ha1,S,δ,hδ,hSE,hS2,hSc,hmass,hsep⟩ := normalized_small_balls X Y u v
    (fun e : E => e.val) Subtype.val_injective hI ha0 he he1 hc₁
    (fun e => ⟨hpositive e.val,hminE e.val e.property⟩) hbnd hcontract
  have hS : S.Nonempty := card_pos.mp (by omega)
  have hSc0 : (0:ℝ) < S.card := by exact_mod_cast (by omega : 0 < S.card)
  have hcard : specα*N'/C ≤ (S.card : ℝ) := by
    apply (div_le_iff₀ hC).mpr
    dsimp [C]
    rw [←mul_div_assoc]
    apply (le_div_iff₀ (sq_pos_of_pos he)).mpr
    rw [hIE] at hSc
    change ε^2*specα*N' ≤ _ at hSc
    nlinarith only [hSc]
  have hcard₂ : (S.card : ℝ) ≤ 2*N' := by
    have hh := card_le_card hSE
    have h1 := card_union_le (univ.image u) (univ.image v)
    have h2 := card_image_le (f := u) (s := univ)
    have h3 := card_image_le (f := v) (s := univ)
    simp only [card_univ,hIE] at h2 h3
    have hSc : S.card ≤ 2*E.card := by omega
    dsimp [N']; exact_mod_cast hSc
  rw [hIE] at hmass
  change (S.card : ℝ)*δ = specα^ε*c₁*N'/C at hmass
  obtain ⟨hηδ,hηc,hlower,hupper,hgain⟩ := StrongThinTree.CaptureNumeric.thresholds
    hs has ha1 he (by linarith : ε ≤ 1/2) hC hN hN' hNle hc₁ hc₂ hSc0 hδ
    hscale hdensity hcard hcard₂ hmass hsmall hR
  let P := T.biUnion (fun t => t.filter (fun w => ∃e ∈ F t, G.left e=w ∨ G.right e=w))
  have hP : ∀w ∈ P, ∃t ∈ T, w ∈ t ∧ ∃e ∈ H.parentBoundary G t,
      (G.left e=w ∨ G.right e=w) ∧ l1dist (X (G.left e)) (X (G.right e)) ≤ c₂ := by
    intro w hw
    obtain ⟨t,ht,hw⟩ := mem_biUnion.mp hw
    obtain ⟨hwt,e,he,hew⟩ := mem_filter.mp hw
    exact ⟨t,ht,hwt,e,hF t ht he,hew,hdmax t ht e he⟩
  have hEnd : ∀e ∈ E, ∃w ∈ P, (G.left e=w ∨ G.right e=w) := by
    intro e he
    obtain ⟨t,ht,het⟩ := mem_biUnion.mp he
    have hc := (mem_filter.mp (hF t ht het)).2
    rcases hc with hc | hc
    · exact ⟨G.left e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inl rfl⟩⟩,Or.inl rfl⟩
    · exact ⟨G.right e,mem_biUnion.mpr ⟨t,ht,mem_filter.mpr ⟨hc.1,e,het,Or.inr rfl⟩⟩,Or.inr rfl⟩
  have hcover : ∀w ∈ S, ∃p ∈ P, l1dist (X w) (X p) ≤ c₂ := by
    intro w hw
    rcases mem_union.mp (hSE hw) with hw | hw
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [u,hp',l1dist_self] using hc₂.le
      · simpa [u,d,hp'] using hmaxE e.val e.property
    · obtain ⟨e,he,rfl⟩ := mem_image.mp hw
      obtain ⟨p,hp,hp'⟩ := hEnd e.val e.property
      refine ⟨p,hp,?_⟩
      rcases hp' with hp' | hp'
      · simpa [v,d,hp',l1dist_comm] using hmaxE e.val e.property
      · simpa [v,hp',l1dist_self] using hc₂.le
  have hNcast : ∑t ∈ T, ((H.parentBoundary G t).card : ℝ) = N := rfl
  have hη : 0 ≤ s^(1+2*ε) := (Real.rpow_pos_of_pos hs _).le
  obtain hcomp | hass := capture_small_balls T S P hS hT hroot hboundary hδ hc₂ hη
    hsep hcover hP hηδ hηc
  · obtain ⟨B,hB⟩ := hcomp
    refine Or.inl ⟨δ,6*max δ (2*c₂),B,hlower,?_,hgain.trans hB⟩
    change 6*max δ (2*c₂) ≤ 12*c₁/s
    calc
      _ ≤ 6*(2*c₁/s) := mul_le_mul_of_nonneg_left hupper (by norm_num)
      _ = 12*c₁/s := by ring
  · obtain ⟨B,hBD,hBT,hB⟩ := hass
    refine Or.inr ⟨B,hBT,?_,?_,hgain.trans hB⟩
    · rw [hBD]
      exact hlower.trans (le_max_left _ _)
    · rw [hBD]
      have hh : 0 ≤ c₁/s := by positivity
      calc
        max δ (2*c₂) ≤ 2*c₁/s := hupper
        _ ≤ 12*c₁/s := by rw [mul_div_assoc,mul_div_assoc]; linarith only [hh]

end
end StrongThinTree.MultiGraph.Hierarchy
end
end OAI
