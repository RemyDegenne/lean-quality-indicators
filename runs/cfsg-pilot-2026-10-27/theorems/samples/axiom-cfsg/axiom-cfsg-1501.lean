public section

namespace CFSG.OddTranspositions.PartThree.Nine

open CFSG.Timmesfeld CFSG.Timmesfeld.Bridge CFSG.Timmesfeld.Bridge.Asc72

open CFSG.Timmesfeld.Connectivity CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G}

section Chain

variable {hC : HypothesisC D} {T : Sylow 2 (Halpha D hC.alpha)} {S : Sylow 2 G}
  {U : Subgroup G} {n : ℕ}

section Component

variable {L L₀ : Subgroup G} {Γ : Set G} {Y : Subgroup G}

theorem eq_of_commute_iff_centralizerComponent (hH : Th91Hyp D hC)
    (h3 : Conclusion9_3 D hC)
    (hU : DeltaSetup hC T S U)
    (hCH : Subgroup.centralizer (Halpha D hC.alpha : Set G) = Subgroup.zpowers hC.d)
    (eH : Halpha D hC.alpha ⧸ Subgroup.center (Halpha D hC.alpha) ≃* PSU3Model n)
    (hUn : Nat.card U = 2 ^ n) (hL : UnitaryCentralizerData hC T S U n L L₀)
    (hΓ : Γ = {d | Reach ((Subgroup.centralizer (L : Set G) : Set G) ∩ D) hC.d d}) :
    ∀ c ∈ Γ, ∀ c' ∈ Γ, (∀ x ∈ Γ, Commute x c ↔ Commute x c') → c = c' := by
  set C := (Subgroup.centralizer (L : Set G) : Set G) ∩ D with hCdef
  obtain ⟨-, hΓC, -, -, hΓcl⟩ := centralizerComponent_facts (Y := Subgroup.closure Γ) hL hΓ rfl
  obtain ⟨X, -, hXu, -, -, hXD, -, -, hZ, -⟩ := exists_psl2_local hH h3 hU hCH eH hUn hL
  have hu2 := hC.setup.oddT.mul_self_eq_one hC.hd
  have huΓ : hC.d ∈ Γ := by
    rw [hΓ]
    exact Relation.ReflTransGen.refl
  intro c hc c' hc' hcc'
  by_contra hne
  have hcc : Commute c c' := (hcc' c hc).mp (Commute.refl c)
  obtain ⟨g, hgN, hgu, hgΓ⟩ := conj_centralizerComponent_of_mem hH h3 hU hCH eH hUn hL hΓ c hc
  have hgc : g⁻¹ * c * g⁻¹⁻¹ = hC.d := by rw [← hgu]; group
  set e := g⁻¹ * c' * g⁻¹⁻¹ with he
  have heC : e ∈ C :=
    conj_mem_centralizer_inter_of_mem_normalizer hC.setup.normal (inv_mem hgN) (hΓC hc')
  have heu : Commute e hC.d := by
    have := (Commute.conj_iff g⁻¹).2 hcc.symm
    rwa [hgc] at this
  have heu1 : e ≠ hC.d := by
    intro h
    apply hne
    calc c = g * hC.d * g⁻¹ := hgu.symm
      _ = g * e * g⁻¹ := by rw [h]
      _ = c' := by rw [he]; group
  obtain ⟨hueX, hue2⟩ := (hXD e).mp ⟨heC, heu, heu1⟩
  have hcent : ∀ t ∈ X, orderOf t = 2 → (hC.d * e) * t = t * (hC.d * e) := by
    intro t htX ht2
    have hut : hC.d * (hC.d * t) = t := by rw [← mul_assoc, hu2, one_mul]
    obtain ⟨hutC, hutu, -⟩ :=
      (hXD (hC.d * t)).mpr ⟨by rw [hut]; exact htX, by rw [hut]; exact ht2⟩
    have hutΓ : hC.d * t ∈ Γ := hΓcl _ huΓ _ hutC hutu
    have h1 : Commute (g * (hC.d * t) * g⁻¹) c := by
      rw [← hgu]
      exact (Commute.conj_iff g).2 hutu
    have h2 := (hcc' _ (hgΓ _ hutΓ)).mp h1
    have h3' : Commute (hC.d * t) e := by
      have := (Commute.conj_iff g⁻¹).2 h2
      rwa [show g⁻¹ * (g * (hC.d * t) * g⁻¹) * g⁻¹⁻¹ = hC.d * t by group] at this
    have hte : t * hC.d = hC.d * t := Subgroup.mem_centralizer_singleton_iff.mp (hXu htX)
    have hte' : t * e = e * t := by
      have h5 : hC.d * (t * e) = hC.d * (e * t) := by
        calc hC.d * (t * e) = (hC.d * t) * e := by group
          _ = e * (hC.d * t) := h3'.eq
          _ = hC.d * (e * t) := by rw [← mul_assoc, heu.eq, mul_assoc]
      exact mul_left_cancel h5
    calc (hC.d * e) * t = hC.d * (e * t) := by group
      _ = hC.d * (t * e) := by rw [hte']
      _ = t * (hC.d * e) := by rw [← mul_assoc, ← hte, mul_assoc]
  have h1 := hZ _ hueX hcent
  rw [h1, orderOf_one] at hue2
  exact absurd hue2 (by decide)

end Component
end Chain
end CFSG.OddTranspositions.PartThree.Nine
end
