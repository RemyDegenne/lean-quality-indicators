open CFSG.LieType.SeitzGeneration

open CFSG.RankThree.PartOne.CTP

open CFSG.Blueprint.Chevalley

open CFSG.LieType.Chevalley

open CFSG.LieType.Steinberg.Adjoint

public section

namespace CFSG.LieType.SeitzGeneration.ExcOuterLeOne

section Close

variable {K : Type} [Field K] [Finite K] {σ η : K ≃+* K} {p : ℕ}

theorem twE6_long_full (hS : TwE6Setup K σ η p) (H : Subgroup ↥(twistedE6RootGroup K σ))
    (hRH : twR σ η ≤ H) {t : K} (hσt : σ t = t) (hηt : η t ≠ t)
    (hmem : xE6 (Pi.single 3 1) t ∈ H.map (twIncl σ)) :
    ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c →
      xE6 (Pi.single i 1) c ∈ H.map (twIncl σ) ∧ xE6 (-Pi.single i 1) c ∈ H.map (twIncl σ) := by
  have hgen : TwGens σ η (twRP σ η) := twR_gens hS
  have hRHP : twRP σ η ≤ H.map (twIncl σ) := Subgroup.map_mono hRH
  have hfixX : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c → η c = c →
      xE6 (Pi.single i 1) c ∈ H.map (twIncl σ) :=
    fun i hi c h1 h2 => hRHP (hgen.fixedX i hi c h1 h2)
  have hfixY : ∀ i ∈ ({1, 3} : Finset (Fin 6)), ∀ c : K, σ c = c → η c = c →
      xE6 (-Pi.single i 1) c ∈ H.map (twIncl σ) :=
    fun i hi c h1 h2 => hRHP (hgen.fixedY i hi c h1 h2)
  have hw : ∀ i ∈ ({1, 3} : Finset (Fin 6)),
      CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6)) i (1 : Kˣ) ∈
        H.map (twIncl σ) := by
    intro i hi
    unfold CFSG.LieType.Steinberg.weylElement
    simp only [inv_one, Units.val_one]
    exact (H.map (twIncl σ)).mul_mem
      ((H.map (twIncl σ)).mul_mem (hfixX i hi 1 (by simp) (by simp))
        (hfixY i hi (-1) (by simp) (by simp)))
      (hfixX i hi 1 (by simp) (by simp))
  have hw1 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6))
      (1 : Fin Tag.E6.rank) (1 : Kˣ) ∈ H.map (twIncl σ) := hw 1 (by decide)
  have hw3 : CFSG.LieType.Steinberg.weylElement (xPar (rootOperatorFamily Tag.E6))
      (3 : Fin Tag.E6.rank) (1 : Kˣ) ∈ H.map (twIncl σ) := hw 3 (by decide)
  have h13 : Tag.E6.cartan 1 3 = -1 := by decide
  have h31 : Tag.E6.cartan 3 1 = -1 := by decide
  obtain ⟨ε, hε, hcomm⟩ := commutator_xPar_neighbour (K := K) (D := e6AdjData)
    e6AdjData_valid noG2_E6 h31 h13
  let A : Subring ↥(fixSubfield σ) :=
    { carrier := {u | xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (u : K) ∈ H.map (twIncl σ)}
      mul_mem' := fun {u v} hu hv => by
        have hu' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (u : K) ∈ H.map (twIncl σ) := hu
        have hv' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (v : K) ∈ H.map (twIncl σ) := hv
        have ha := (twE6_neighbour_one_three (H.map (twIncl σ)) hw1 hw3 (u : K)).mp hu'
        have hm := xPar_mul_mem_of_commutator (H.map (twIncl σ)) hε hcomm ha hv'
        rw [add_comm] at hm
        exact (twE6_mem_e13_iff (H.map (twIncl σ)) hw1 ((u : K) * (v : K))).mpr hm
      one_mem' := by
        show xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) ((1 : ↥(fixSubfield σ)) : K) ∈
          H.map (twIncl σ)
        rw [OneMemClass.coe_one]
        exact hfixX 3 (by decide) 1 (by simp) (by simp)
      add_mem' := fun {u v} hu hv => by
        have hu' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (u : K) ∈ H.map (twIncl σ) := hu
        have hv' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (v : K) ∈ H.map (twIncl σ) := hv
        show xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) ((u + v : ↥(fixSubfield σ)) : K) ∈
          H.map (twIncl σ)
        rw [AddMemClass.coe_add, xPar_add]
        exact (H.map (twIncl σ)).mul_mem hu' hv'
      zero_mem' := by
        show xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) ((0 : ↥(fixSubfield σ)) : K) ∈
          H.map (twIncl σ)
        rw [ZeroMemClass.coe_zero, xPar_zero]
        exact (H.map (twIncl σ)).one_mem
      neg_mem' := fun {u} hu => by
        have hu' : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) (u : K) ∈ H.map (twIncl σ) := hu
        show xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) ((-u : ↥(fixSubfield σ)) : K) ∈
          H.map (twIncl σ)
        rw [NegMemClass.coe_neg, ← xPar_neg]
        exact (H.map (twIncl σ)).inv_mem hu' }
  have htF : t ∈ fixSubfield σ := hσt
  have hk : ∀ F' : Subfield ↥(fixSubfield σ), fixSubfield (fixSubfieldRestrict η σ) ≤ F' →
      F' = fixSubfield (fixSubfieldRestrict η σ) ∨ F' = ⊤ :=
    fun F' hF' => subfield_eq_or_top (fixSubfieldRestrict η σ) hS.prime
      (TwE6Setup.orderOf_restrict hS) F' hF'
  have hkS : ∀ c ∈ fixSubfield (fixSubfieldRestrict η σ), c ∈ A := by
    intro c hc
    rw [mem_fixSubfield] at hc
    have hηc : η (c : K) = (c : K) := by
      have h := congrArg Subtype.val hc
      rw [coe_fixSubfieldRestrict] at h
      exact h
    exact hfixX 3 (by decide) (c : K) c.2 hηc
  have ht : (⟨t, htF⟩ : ↥(fixSubfield σ)) ∉ fixSubfield (fixSubfieldRestrict η σ) := by
    intro h
    rw [mem_fixSubfield] at h
    apply hηt
    have h' := congrArg Subtype.val h
    rw [coe_fixSubfieldRestrict] at h'
    exact h'
  have htA : (⟨t, htF⟩ : ↥(fixSubfield σ)) ∈ A := hmem
  have hA : A = ⊤ := eq_top_of_subring (fixSubfield (fixSubfieldRestrict η σ)) hk A hkS ht htA
  intro i hi c hc
  have hcA : (⟨c, (show c ∈ fixSubfield σ from hc)⟩ : ↥(fixSubfield σ)) ∈ A := by
    rw [hA]
    exact Subring.mem_top _
  have h3 : xPar (rootOperatorFamily Tag.E6) (Pi.single 3 1) c ∈ H.map (twIncl σ) := hcA
  have h1 : xPar (rootOperatorFamily Tag.E6) (Pi.single 1 1) c ∈ H.map (twIncl σ) :=
    (twE6_neighbour_one_three (H.map (twIncl σ)) hw1 hw3 c).mp h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi
  rcases hi with rfl | rfl
  · refine ⟨h1, ?_⟩
    have h := (twE6_mem_reflect_node (H.map (twIncl σ)) hw1 (isRoot_single Tag.E6 1) c).mp h1
    rwa [twE6_reflect_self 1] at h
  · refine ⟨h3, ?_⟩
    have h := (twE6_mem_reflect_node (H.map (twIncl σ)) hw3 (isRoot_single Tag.E6 3) c).mp h3
    rwa [twE6_reflect_self 3] at h

end Close
end CFSG.LieType.SeitzGeneration.ExcOuterLeOne
end
