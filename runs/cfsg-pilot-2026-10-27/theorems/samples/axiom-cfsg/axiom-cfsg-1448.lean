public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.Torsion37 CFSG.RankThree.PartOne.Planes

open scoped commutatorElement

variable {G : Type} [Group G]

section Eleven

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem data_of_inputs (h124 : Node124) (h125 : Node125) (h : Sec12Hyp G p A c L E)
    (hX : torusWeylHasPCore p E) (hfix : pCoreFixed p E = E ⊓ L)
    (hcard : Nat.card E = p * Nat.card ↥(E ⊓ L)) (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    Sec1211.Data p (torusWeyl E).subtype ((E ⊓ L).subgroupOf E) (CFSG.pCore p ↥(torusWeyl E)) := by
  have hp := h.prime
  have hcL : c ∉ L := Sec12Three.c_not_mem_L h hZ
  have hBle : E ⊓ L ≤ E := inf_le_left
  have hmemB : ∀ b : ↥E, b ∈ (E ⊓ L).subgroupOf E ↔ (b : G) ∈ E ⊓ L := fun b =>
    Subgroup.mem_subgroupOf
  refine
    { prime := hp
      comm := fun a b => h.E_elem.is_comm.comm a b
      pow_eq_one := fun a => Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h a.2)
      card_eq := ?_
      α_inj := Subtype.val_injective
      X_normal := fun w x hx =>
        (CFSG.pCore_normal (p := p) (G := ↥(torusWeyl E))).conj_mem x hx w
      X_pgroup := CFSG.pCore_isPGroup
      X_fixes := ?_
      B_inv := ?_
      B_irr := ?_
      X_ne_bot := hX }
  · exact hcard.trans (congrArg (p * ·)
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv.symm))
  · intro x hx b hb
    exact (mem_pCoreFixed.1 (hfix.ge ((hmemB b).1 hb))).2 x hx
  · intro w b hb
    have hinv := (LinAlg.torusInvariant_top_iff_forall_torusWeyl (pCoreFixed_le p E)).1
      (torusInvariant_pCoreFixed p E) (w : MulAut E) w.2 b (hfix.ge ((hmemB b).1 hb))
    exact (hmemB _).2 (hfix.le hinv)
  · intro S hS hSinv
    have hS'E : S.map E.subtype ≤ E := Subgroup.map_subtype_le S
    have hS'B : S.map E.subtype ≤ E ⊓ L := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
      exact (hmemB s).1 (hS hs)
    have hinvW : torusInvariant E ⊤ (S.map E.subtype) := by
      rw [LinAlg.torusInvariant_top_iff_forall_torusWeyl hS'E]
      intro φ hφ b hb
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hb
      exact Subgroup.mem_map.2 ⟨(torusWeyl E).subtype ⟨φ, hφ⟩ s, hSinv ⟨φ, hφ⟩ s hs, rfl⟩
    have hinvL : torusInvariant E L (S.map E.subtype) := fun w hw =>
      hinvW w ⟨Subgroup.mem_top w, hw.2⟩
    by_cases hS0 : S.map E.subtype = ⊥
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective S E.subtype_injective).1 hS0
    · right
      have hS'ne : S.map E.subtype ≠ E := fun heq =>
        pCoreFixed_ne_top hX (le_antisymm (pCoreFixed_le p E)
          (heq.symm.le.trans (hS'B.trans hfix.ge)))
      rcases (h124 G p A c L E h).1 _ hS'E hinvL hS0 hS'ne with hc | hc
      · exfalso
        have hcS : c ∈ S.map E.subtype := hc ▸ Subgroup.mem_zpowers c
        exact hcL (Subgroup.mem_inf.1 (hS'B hcS)).2
      · apply Subgroup.map_injective E.subtype_injective
        calc S.map E.subtype = ⁅E, L ⊓ torusNormalizer E⁆ := hc
          _ = pCoreFixed p E := (pCoreFixed_eq_commutator h124 h125 h hX).symm
          _ = E ⊓ L := hfix
          _ = ((E ⊓ L).subgroupOf E).map E.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hBle).symm

end Eleven
end CFSG.RankThree.PartOne
end
