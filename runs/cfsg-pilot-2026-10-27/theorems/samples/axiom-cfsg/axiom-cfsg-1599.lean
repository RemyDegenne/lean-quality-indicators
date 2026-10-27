public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki

open CFSG.ClassicalInvolution.Q3.AE CFSG.ClassicalInvolution.Q3.AE.Wr

open CFSG.ClassicalInvolution.Sp62Rec.I1 CFSG.ClassicalInvolution.Sp62Rec Equiv CFSG.Open

open CFSG.ClassicalInvolution.Solomon73 CFSG.ClassicalInvolution.Solomon73.Yamaki

section Certs

namespace YData

variable {G : Type} [Group G] [Finite G] {z : G} (Y : YData z)

theorem nonempty_fusionOut_of_std (hchar : IsCharTwoType G) (P : Sylow 2 G)
    (hP : (P : Subgroup G) = Y.T) (hz : orderOf z = 2) (h3 : ¬ IsConj z Y.π3)
    (h12 : ¬ IsConj z Y.π12) (hE : ∀ B : Subgroup G, B ≤ Y.T → IsE64 B → B = Y.A)
    (hstd : Y.coord (conjSet Y.NA z) = scOrb 0 ∪ scOrb 6) : Nonempty (FusionOut z) := by
  obtain ⟨Θ, hΘα, hΘD, hΘS⟩ := exists_thetaW
  obtain ⟨c, hc, hL⟩ := Y.exists_perm_l32 hstd
  set b : Fin 7 → G := fun j => Y.σA (bW (c⁻¹ j)) with hb
  have hbz : b (c 0) = z := by
    simp only [hb, p7_inv_apply, bW_zero, sc012_eq, Y.σA_one_zero]
  have hb_orbit : ∀ x, (∃ n ∈ Subgroup.normalizer (Y.A : Set G), n * z * n⁻¹ = x) ↔
      ∃ i, b i = x := by
    intro x
    constructor
    · intro hx
      have hxN : x ∈ conjSet Y.NA z := hx
      have hxA := conjSet_normalizer_subset Y.z_mem_A hxN
      have hF : Y.coordOf x ∈ scOrb 0 ∪ scOrb 6 := by
        rw [← Y.mem_conj_z_iff hstd, Y.σA_coordOf hxA]
        exact hxN
      obtain ⟨k, hk⟩ := (mem_Omega_iff _).mp hF
      refine ⟨c k, ?_⟩
      simp only [hb, p7_inv_apply, hk, Y.σA_coordOf hxA]
    · rintro ⟨i, rfl⟩
      exact (Y.mem_conj_z_iff hstd _).mpr ((mem_Omega_iff _).mpr ⟨_, rfl⟩)
  have hsum_mem : ∀ s : Finset (Fin 7), Y.σA (∑ j ∈ s, bW j) ∈ Subgroup.closure (Set.range b) := by
    intro s
    classical
    induction s using Finset.induction_on with
    | empty => rw [Finset.sum_empty, Y.σA_zero]; exact Subgroup.one_mem _
    | insert a s ha ih =>
      rw [Finset.sum_insert ha, Y.σA_add]
      refine Subgroup.mul_mem _ (Subgroup.subset_closure ⟨c a, ?_⟩) ih
      simp only [hb, p7_inv_apply]
  have hb_closure : Subgroup.closure (Set.range b) = Y.A := by
    refine le_antisymm ((Subgroup.closure_le _).mpr ?_) fun x hx => ?_
    · rintro _ ⟨i, rfl⟩
      exact Y.σA_mem_A _
    · obtain ⟨x0, rfl⟩ := Y.exists_σA hx
      obtain ⟨s, rfl⟩ := exists_sum_bW x0
      exact hsum_mem s
  have hb_prod : (List.ofFn b).prod = 1 := by
    rw [show b = fun j => Y.σA (bW (c⁻¹ j)) from rfl, Y.prod_ofFn_σA,
      Equiv.sum_comp c⁻¹ bW, sum_bW, Y.σA_zero]
  have hb_perm : ∀ n ∈ Subgroup.normalizer (Y.A : Set G), ∃ σ ∈ l32, ∀ i,
      n * b i * n⁻¹ = b (σ i) := by
    intro n hn
    refine ⟨c * Y.permHom hstd ⟨n, hn⟩ * c⁻¹, hL ⟨n, hn⟩, fun i => ?_⟩
    simp only [hb]
    rw [← Y.σA_cc hn, ← Y.bW_permHom hstd ⟨n, hn⟩]
    simp only [Perm.mul_apply, p7_inv_apply]
  have hgen : Subgroup.closure {x | x ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf x = 2} =
      Subgroup.centralizer ({z} : Set G) := by
    refine le_antisymm ((Subgroup.closure_le _).mpr fun x hx => hx.1) ?_
    set I := Subgroup.closure {x | x ∈ Subgroup.centralizer ({z} : Set G) ∧ orderOf x = 2}
      with hI
    have key : ∀ m ∈ Hhat, ∀ hm : m ∈ Hhat, (((Y.ϑ.trans Θ).symm ⟨m, hm⟩ :
        ↥(Subgroup.centralizer ({z} : Set G))) : G) ∈ I := by
      intro m hm0
      induction hm0 using Subgroup.closure_induction with
      | mem y hy =>
        intro hm
        obtain ⟨i, -, rfl⟩ := hy
        set y' := (Y.ϑ.trans Θ).symm ⟨yamakiSp i, hm⟩
        have hsq : (y' : G) * y' = 1 := by
          have h1 : (Y.ϑ.trans Θ).symm (⟨yamakiSp i, hm⟩ * ⟨yamakiSp i, hm⟩) = 1 := by
            have : (⟨yamakiSp i, hm⟩ * ⟨yamakiSp i, hm⟩ : ↥Hhat) = 1 :=
              Subtype.ext (yamakiSp_mul_self i)
            rw [this, map_one]
          rw [map_mul] at h1
          exact congrArg Subtype.val h1
        by_cases h1 : (y' : G) = 1
        · rw [h1]
          exact I.one_mem
        · exact Subgroup.subset_closure ⟨y'.2, orderOf_eq_prime (by rw [sq]; exact hsq) h1⟩
      | one =>
        intro hm
        have e : (⟨1, hm⟩ : ↥Hhat) = 1 := rfl
        rw [e, map_one]
        exact I.one_mem
      | mul a b' ha hb' iha ihb =>
        intro hm
        have e : (⟨a * b', hm⟩ : ↥Hhat) = ⟨a, ha⟩ * ⟨b', hb'⟩ := rfl
        rw [e, map_mul, Subgroup.coe_mul]
        exact I.mul_mem (iha ha) (ihb hb')
      | inv a ha iha =>
        intro hm
        have e : (⟨a⁻¹, hm⟩ : ↥Hhat) = (⟨a, ha⟩)⁻¹ := rfl
        rw [e, map_inv, Subgroup.coe_inv]
        exact I.inv_mem (iha ha)
    intro x hx
    have h := key _ ((Y.ϑ.trans Θ) ⟨x, hx⟩).2 ((Y.ϑ.trans Θ) ⟨x, hx⟩).2
    rwa [Subtype.coe_eta, MulEquiv.symm_apply_apply] at h
  obtain ⟨hU1, hU2, hU3⟩ := Y.compl_A
  refine ⟨{
    θ := Y.ϑ.trans Θ
    θ_z := ?_
    T := P
    T_le := hP ▸ Y.T_le_C
    θ_T := fun x hx => by rw [hP]; exact Y.theta_T hΘD x hx
    A := Y.A
    A_le := Y.A_le_C
    θ_A := Y.theta_A hΘS
    cent_A := Y.centralizer_A_le
    b := b
    b_inj := fun i j h => c⁻¹.injective (bW_injective (Y.σA_injective h))
    z_mem := ⟨c 0, hbz⟩
    b_orbit := hb_orbit
    b_prod := hb_prod
    b_closure := hb_closure
    perm_mem := hb_perm
    card_N := Y.card_NA hstd
    compl := ⟨Y.U, hP ▸ hU1, hU2, hP ▸ hU3⟩
    cent_le := fun x hx hx1 =>
      Y.centralizer_le_K hstd hc hL hchar P hP hE hz h3 h12 hx hx1
    conj_A := fun t ht ht2 => Y.exists_conj_mem_A (hP ▸ ht)
      (by rw [← sq, ← ht2, pow_orderOf_eq_one])
    gen_inv := hgen }⟩
  show ((Θ (Y.ϑ ⟨z, _⟩) : ↥Hhat) : StatedSp 3 (ZMod 2)) = alpha
  rw [show Y.ϑ ⟨z, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩ =
    ⟨Wr.allOnes 6, allOnes_mem_Wsub⟩ from Subtype.ext Y.ϑ_z]
  exact hΘα

end YData
end Certs
end CFSG.RankThree.PartTwo.Sec19.SolEven.Yamaki
end
