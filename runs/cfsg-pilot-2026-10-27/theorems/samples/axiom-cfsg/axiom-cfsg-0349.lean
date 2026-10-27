public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.S152X

open CFSG.Quasithin.F7 CFSG.Quasithin.FA5

open CFSG.Quasithin.F53

open CFSG.Quasithin.CosetGeom

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

section B5

variable (F : Frame L1 L2 S D X)

include F

theorem three_fix_path5
    (hPU : ¬ P1 L1 L2 S ≤ Subgroup.normalizer ((Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) : Set G))
    {a0 a1 a2 a3 a4 : Geo (P1 L1 L2 S) (P2 L1 L2 S)}
    (h0 : (graph _ _ _).Adj a0 a1) (h1 : (graph _ _ _).Adj a1 a2)
    (h2 : (graph _ _ _).Adj a2 a3) (h3 : (graph _ _ _).Adj a3 a4)
    (hv0 : vtype a0 = false) (n02 : a0 ≠ a2) (n13 : a1 ≠ a3) (n24 : a2 ≠ a4) :
    ∃ t : G, t ∈ stab a0 ∧ t ∈ stab a4 ∧ t ^ 3 = 1 ∧ t ≠ 1 := by
  have hA := Amal.of_frame F
  have ty : ∀ {a b : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, (graph _ _ _).Adj a b →
      vtype a = false → vtype b = true := by
    intro a b hab ha
    have := vtype_ne_of_adj hab
    cases hv : vtype b <;> simp_all
  have ty' : ∀ {a b : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, (graph _ _ _).Adj a b →
      vtype a = true → vtype b = false := by
    intro a b hab ha
    have := vtype_ne_of_adj hab
    cases hv : vtype b <;> simp_all
  have hv1 : vtype a1 = true := ty h0 hv0
  have hv2 : vtype a2 = false := ty' h1 hv1
  have hv3 : vtype a3 = true := ty h2 hv2
  have hv4 : vtype a4 = false := ty' h3 hv3
  obtain ⟨t, -, ht1', ht3, hta0, hta2⟩ :=
    exists_three_stab_two_nbrs F hv1 (show a0 ∈ nbrs a1 from h0.symm)
      (show a2 ∈ nbrs a1 from h1) n02
  have hta3 : t ∈ stab a3 := three_mem_stab_nbr F hv2 (show a3 ∈ nbrs a2 from h2) hta2 ht3
  have hcard := card_fixed_nbrs_three F hv3 hta3 ht3 ht1'
  obtain ⟨w, hwn, hwt, hwv2⟩ : ∃ w : Geo (P1 L1 L2 S) (P2 L1 L2 S), w ∈ nbrs a3 ∧ t ∈ stab w ∧
      w ≠ a2 := by
    by_contra hcon
    push Not at hcon
    have hsub : Subsingleton {μ : Geo (P1 L1 L2 S) (P2 L1 L2 S) // μ ∈ nbrs a3 ∧ t ∈ stab μ} :=
      ⟨fun a b => Subtype.ext ((hcon a.1 a.2.1 a.2.2).trans (hcon b.1 b.2.1 b.2.2).symm)⟩
    have := Finite.card_le_one_iff_subsingleton.mpr hsub
    omega
  obtain ⟨q, hqQ, hqw⟩ := exists_Qv_smul_nbr F hv3 (show a2 ∈ nbrs a3 from h2.symm) hwn
    (show a4 ∈ nbrs a3 from h3) hwv2 n24.symm
  have hsup := Qv_le_sup_of_not_normal F hPU hv2 (show a1 ∈ nbrs a2 from h1.symm)
    (show a3 ∈ nbrs a2 from h2) n13
  have hQN : ∀ {δ μ : Geo (P1 L1 L2 S) (P2 L1 L2 S)}, μ ∈ nbrs δ →
      Qv δ ≤ Subgroup.normalizer ((Qv μ : Subgroup G) : Set G) := fun {δ μ} hμ =>
    (hA.Qv_le_stab_of_mem_nbrs hμ).trans (le_normalizer_pCoreOf 2 (stab μ))
  have hQs : ∀ δ : Geo (P1 L1 L2 S) (P2 L1 L2 S), Qv δ ≤ stab δ := fun δ => pCoreOf_le 2 (stab δ)
  have hNy : (Qv a2 ⊓ Qv a3) ≤ Subgroup.normalizer ((Qv a2 ⊓ Qv a1 : Subgroup G) : Set G) := by
    refine le_normalizer_inf (inf_le_left.trans ?_) (inf_le_left.trans ?_)
    · exact (hQs a2).trans (le_normalizer_pCoreOf 2 (stab a2))
    · exact hQN (show a1 ∈ nbrs a2 from h1.symm)
  obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hNy).mp (hsup hqQ)
  have haG : (a : G) ∈ stab a2 := hQs a2 ha.1
  have hbG : (b : G) ∈ stab a3 := hQs a3 hb.2
  obtain ⟨haG0, -⟩ := mem_stab.mp haG
  obtain ⟨hbG0, -⟩ := mem_stab.mp hbG
  set ya : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨a, haG0⟩ with hya
  set yb : ↥(P1 L1 L2 S ⊔ P2 L1 L2 S) := ⟨b, hbG0⟩ with hyb
  have hq_eq : q = ya * yb := Subtype.ext hab
  have hybw : yb • w = w :=
    smul_eq_of_mem_stab (hA.Qv_le_stab_of_mem_nbrs hwn hb.2)
  have hyaw : ya • w = a4 := by
    rw [← hqw, hq_eq, mul_smul, hybw]
  have hyaa0 : ya • a0 = a0 :=
    smul_eq_of_mem_stab (hA.Qv_le_stab_of_mem_nbrs (show a0 ∈ nbrs a1 from h0.symm) ha.2)
  have ht'a0 : (a : G) * t * (a : G)⁻¹ ∈ stab a0 := conj_mem_stab_of_fix ya hyaa0 hta0
  have ht'w : (a : G) * t * (a : G)⁻¹ ∈ stab a4 := by
    have h1' : (a : G) * t * (a : G)⁻¹ ∈ stab (ya • w) := by
      rw [stab_smul]; exact mem_conjSub_of_mem' hwt
    rwa [hyaw] at h1'
  have ht'3 : ((a : G) * t * (a : G)⁻¹) ^ 3 = 1 := by rw [conj_pow, ht3]; group
  have ht'1 : (a : G) * t * (a : G)⁻¹ ≠ 1 := by
    intro h
    apply ht1'
    have : t = (a : G)⁻¹ * ((a : G) * t * (a : G)⁻¹) * a := by group
    rw [this, h]; group
  exact ⟨_, ht'a0, ht'w, ht'3, ht'1⟩

end B5
end CFSG.Quasithin.Kleidman.F204
end
