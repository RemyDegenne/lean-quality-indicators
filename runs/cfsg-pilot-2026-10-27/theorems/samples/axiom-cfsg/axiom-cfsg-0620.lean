public section

namespace CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6

open Subgroup CFSG.Open CFSG.EvenSporadicStandard.M24Std CFSG.EvenSporadicStandard.M23Std

theorem Config.fusionOddCore_eq_bot_of_cent {V : Type} [Group V] (hc : ∀ x y : V, x * y = y * x)
    (hs : ∀ x : V, x * x = 1) (hV : Nat.card V = 256) {G : Type} [Group G] [Finite G]
    {ρ : G →* MulAut V} (hρ : Function.Injective ρ) (c : Config ρ)
    (hcent : ∀ g : MulAut V, (∀ x ∈ c.C ⊔ c.D, g * ρ x = ρ x * g) → g = 1) :
    fusionOddCore G = ⊥ := by
  classical
  by_contra hne
  have hFT : OddSolv := fun _ _ _ h => CFSG.FeitThompson.isSolvable_of_odd_natCard _ h
  have hNodd : Odd (Nat.card (fusionOddCore G)) := natCard_fusionOddCore_odd G
  obtain ⟨M, ⟨hMn, hMN, hMne⟩, hmin⟩ := WellFounded.has_min
    (wellFounded_lt (α := Subgroup G))
    {K : Subgroup G | K.Normal ∧ K ≤ fusionOddCore G ∧ K ≠ ⊥} ⟨fusionOddCore G, inferInstance,
      le_rfl, hne⟩
  have := hMn
  have hModd : Odd (Nat.card M) := Odd.of_dvd_nat hNodd (Subgroup.card_dvd_of_le hMN)
  have hchief : ∀ K : Subgroup G, K.Normal → ⊥ ≤ K → K ≤ M → K = ⊥ ∨ K = M := by
    intro K hK _ hKM
    by_cases hK0 : K = ⊥
    · exact Or.inl hK0
    · right
      have := hmin K ⟨hK, hKM.trans hMN, hK0⟩
      exact (lt_or_eq_of_le hKM).resolve_left this
  obtain ⟨p, r, hp, hp2, hcardW, hexp, hcommW⟩ :=
    chief_elemAb hFT (bot_le : (⊥ : Subgroup G) ≤ M) (Ne.symm hMne) hModd hchief
  have hinj : Function.Injective (QuotientGroup.mk' (⊥ : Subgroup G)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
  have hcardM : Nat.card M = p ^ r := by
    rw [← hcardW, chiefW, Subgroup.card_map_of_injective hinj]
  have hMCD : M ⊓ (c.C ⊔ c.D) = ⊥ := by
    refine eq_bot_iff.2 fun x hx => ?_
    have := c.inf_odd
    have hx' : x ∈ (c.C ⊔ c.D) ⊓ fusionOddCore G := ⟨hx.2, hMN hx.1⟩
    rw [c.inf_odd] at hx'
    exact hx'
  have hdvd1 : Nat.card ↥(c.C ⊔ c.D) ∣ Nat.card (G ⧸ M) := by
    refine Subgroup.card_dvd_of_injective ((QuotientGroup.mk' M).comp (c.C ⊔ c.D).subtype) ?_
    rw [← MonoidHom.ker_eq_bot_iff]
    refine eq_bot_iff.2 fun x hx => ?_
    have hx1 : (x : G) ∈ M := (QuotientGroup.eq_one_iff _).1 hx
    have : (x : G) ∈ M ⊓ (c.C ⊔ c.D) := ⟨hx1, x.2⟩
    rw [hMCD] at this
    exact Subtype.ext ((Subgroup.mem_bot).1 this)
  have hdvd2 : Nat.card G = Nat.card (G ⧸ M) * Nat.card M :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup M
  have hgl := M22Std.card_dvd_gl8 hc hs hV ρ hρ
  have hdiv : 129600 * p ^ r ∣ 129600 * (2 ^ 22 * 9838563) := by
    have h1 : 129600 * p ^ r ∣ Nat.card G := by
      rw [c.card_sup] at hdvd1
      rw [← hcardM, hdvd2]
      exact Nat.mul_dvd_mul hdvd1 dvd_rfl
    refine h1.trans (hgl.trans ?_)
    unfold M22Std.gl8
    norm_num
  have hdiv2 : p ^ r ∣ 2 ^ 22 * 9838563 := Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdiv
  have hcop : Nat.Coprime (p ^ r) (2 ^ 22) :=
    Nat.Coprime.pow _ _ ((Nat.coprime_primes hp Nat.prime_two).2 hp2)
  have hdiv3 : p ^ r ∣ 9838563 := hcop.dvd_of_dvd_mul_left hdiv2
  have hr1 : 1 ≤ r := by
    by_contra h0
    have hr0 : r = 0 := by omega
    rw [hr0, pow_zero] at hcardM
    exact hMne (Subgroup.card_eq_one.1 hcardM)
  have : Finite (chiefW ⊥ M) := inferInstance
  have hno : ¬ 360 ∣ Nat.card (MulAut (chiefW ⊥ M)) :=
    not_dvd_card_mulAut hcommW hp hdiv3 hr1 hexp hcardW
  have hCc := comm_of_alt6 (M := M) c.eC hno
  have hDc := comm_of_alt6 (M := M) c.eD hno
  have hle : c.C ⊔ c.D ≤ centralizer (M : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [mem_centralizer_iff]
      intro m hm
      exact (hCc x hx m hm).symm
    · rw [mem_centralizer_iff]
      intro m hm
      exact (hDc x hx m hm).symm
  apply hMne
  refine eq_bot_iff.2 fun m hm => ?_
  have h1 : ρ m = 1 := by
    apply hcent
    intro x hx
    have := mem_centralizer_iff.1 (hle hx) m hm
    rw [← map_mul, ← map_mul, this]
  rw [Subgroup.mem_bot]
  exact hρ (by rw [h1, map_one])

end CFSG.EvenSporadicStandard.HSStd.Zassenhaus.A6A6
end
