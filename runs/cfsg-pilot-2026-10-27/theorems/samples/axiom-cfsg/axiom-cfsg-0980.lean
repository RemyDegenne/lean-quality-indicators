public section

namespace CFSG.Combinatorics.QuadrangleGraph

variable {α : Type*} {adj : α → α → Prop}

namespace IsQuadrangleOfOrder

variable [Fintype α] {s t p : ℕ}

theorem card_filter_adj_of_mem_perp2 [DecidableRel adj] (h : IsQuadrangleOfOrder adj s t)
    (ht : 1 ≤ t) {x y : α} (hxy : ¬ adj x y) (hp : (span2 adj x y).card = p + 1)
    {O : Finset α} (hO : ∀ w, w ∈ O ↔ ∀ u ∈ span2 adj x y, ¬ adj w u) {z : α}
    (hz : z ∈ perp2 adj x y) :
    (O.filter fun w => adj w z).card + (p + 1) * s = (t + 1) * s := by
  classical
  have hzx : adj z x := (mem_perp2.1 hz).1
  have hzy : adj z y := (mem_perp2.1 hz).2
  have hVne : (span2 adj x y).Nonempty := ⟨x, h.toIsQuadrangle.left_mem_span2 x y⟩
  have hC : ∀ u ∈ span2 adj x y, ({z} : Finset α) ⊆ perp2 adj z u := by
    intro u hu w hw
    rw [Finset.mem_singleton] at hw
    subst w
    exact mem_perp2.2 ⟨h.toIsQuadrangle.refl z,
      h.toIsQuadrangle.symm ((mem_span2.1 hu) z hzx hzy)⟩
  have hL : ∀ u ∈ span2 adj x y, ∀ v ∈ span2 adj x y, u ≠ v →
      perp2 adj z u ∩ perp2 adj z v ⊆ ({z} : Finset α) := by
    intro u hu v hv huv w hw
    rw [Finset.mem_inter, mem_perp2, mem_perp2] at hw
    obtain ⟨⟨hwz, hwu⟩, ⟨-, hwv⟩⟩ := hw
    by_contra hwne
    rw [Finset.mem_singleton] at hwne
    exact (h.not_adj_of_mem_span2 ht hxy hu hv huv)
      (h.toIsQuadrangle.clique (Ne.symm hwne) (h.toIsQuadrangle.symm hwz)
        ((mem_span2.1 hu) z hzx hzy) (h.toIsQuadrangle.symm hwu)
        ((mem_span2.1 hv) z hzx hzy) (h.toIsQuadrangle.symm hwv))
  have hm : ∀ u ∈ span2 adj x y, (perp2 adj z u).card = s + 1 := by
    intro u hu
    have hzu : z ≠ u := fun e => (h.notMem_span2_of_mem_perp2 ht hxy hz) (e.symm ▸ hu)
    exact h.card_line hzu (h.toIsQuadrangle.symm ((mem_span2.1 hu) z hzx hzy))
  have hsun := card_biUnion_add_card_mul (S := span2 adj x y) (L := fun u => perp2 adj z u)
    (C := ({z} : Finset α)) (m := s + 1) hVne hC hL hm
  rw [Finset.card_singleton, Nat.mul_one, hp, Nat.mul_succ] at hsun
  have hUsub : (span2 adj x y).biUnion (fun u => perp2 adj z u) ⊆ nbhd adj z := by
    intro w hw
    obtain ⟨u, -, hwu⟩ := Finset.mem_biUnion.1 hw
    rw [mem_nbhd]
    exact h.toIsQuadrangle.symm (mem_perp2.1 hwu).1
  have hfilter : O.filter (fun w => adj w z) =
      nbhd adj z \ (span2 adj x y).biUnion (fun u => perp2 adj z u) := by
    ext w
    rw [Finset.mem_filter, Finset.mem_sdiff, mem_nbhd, Finset.mem_biUnion, hO w]
    constructor
    · rintro ⟨hOw, hwz⟩
      exact ⟨h.toIsQuadrangle.symm hwz, fun hwu => by
        obtain ⟨u, hu, hwu'⟩ := hwu
        exact hOw u hu (mem_perp2.1 hwu').2⟩
    · rintro ⟨hzw, hnot⟩
      refine ⟨fun u hu hwu => hnot ⟨u, hu, mem_perp2.2 ⟨h.toIsQuadrangle.symm hzw, hwu⟩⟩,
        h.toIsQuadrangle.symm hzw⟩
  have hcard := Finset.card_sdiff_add_card_eq_card hUsub
  rw [← hfilter, h.card_nbhd z] at hcard
  linarith

end IsQuadrangleOfOrder
end CFSG.Combinatorics.QuadrangleGraph
end
