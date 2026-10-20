@[expose] public section

namespace SaxlCounterexamples.EveryBase

open scoped BigOperators

/-- Every affine element has an odd invariant cycle avoiding zero once
`d ≥ 3`.  This lower bound is necessary: a nonzero translation is transitive
on `GF(3)` when `d = 1`. -/
noncomputable def hqAvoidingCycle (d : Nat) (hd : Odd d) (hd3 : 3 ≤ d)
    (g : Hq d) : AvoidingCycle (Hq d) (Fq d) g 0 := by
  classical
  by_cases hright : g.right = 1
  · by_cases hleft : g.left.toAdd = 0
    · refine {
        carrier := {1}
        avoids := by simp
        odd_card := by simp
        invariant := ?_ }
      intro x
      have hg_one : g = 1 := by
        apply SemidirectProduct.ext
        · apply Multiplicative.toAdd.injective
          simpa using hleft
        · simpa using hright
      simp [hg_one]
    · let b : Fq d := g.left.toAdd
      have hb0 : b ≠ 0 := hleft
      have hcardq : Fintype.card (Fq d) = 3 ^ d := by
        rw [Fintype.card_eq_nat_card, fq_card d hd]
      have hpow : 27 ≤ 3 ^ d := by
        have hp := Nat.pow_le_pow_right (n := 3) (by omega) hd3
        norm_num at hp ⊢
        exact hp
      let forbidden : Finset (Fq d) := {0, b, -b}
      have hforbidden : forbidden.card ≤ 3 := by
        dsimp [forbidden]
        calc
          ({0, b, -b} : Finset (Fq d)).card ≤
              ({b, -b} : Finset (Fq d)).card + 1 :=
            Finset.card_insert_le _ _
          _ ≤ ({-b} : Finset (Fq d)).card + 1 + 1 :=
            Nat.add_le_add_right (Finset.card_insert_le _ _) 1
          _ = 3 := by simp
      have hex : ∃ x : Fq d, x ∉ forbidden := by
        have hnotall : ¬ ∀ x : Fq d, x ∈ forbidden := by
          intro hall
          have hsub : (Finset.univ : Finset (Fq d)) ⊆ forbidden := by
            intro y _hy
            exact hall y
          have hc := Finset.card_le_card hsub
          rw [Finset.card_univ, hcardq] at hc
          omega
        exact not_forall.mp hnotall
      let x := Classical.choose hex
      have hx : x ∉ forbidden := Classical.choose_spec hex
      have hx0 : x ≠ 0 := by
        intro h
        apply hx
        simp [forbidden, h]
      have hxb : x ≠ b := by
        intro h
        apply hx
        simp [forbidden, h]
      have hxnb : x ≠ -b := by
        intro h
        apply hx
        simp [forbidden, h]
      have hbb : b + b = -b := char_three_add_self d b
      have gsmul (y : Fq d) : g • y = b + y := by
        simp [Saxl.affine_smul_def, b, hright]
      have hcycle0 : g • x = x + b := by
        rw [gsmul]
        ring
      have hcycle1 : g • (x + b) = x - b := by
        rw [gsmul]
        linear_combination hbb
      have hcycle2 : g • (x - b) = x := by
        rw [gsmul]
        ring
      have hx_add_ne_x : x + b ≠ x := by
        intro h
        apply hb0
        apply add_left_cancel (a := x)
        simpa using h
      have hx_sub_ne_x : x - b ≠ x := by
        intro h
        exact hb0 (sub_eq_self.mp h)
      have hx_add_ne_sub : x + b ≠ x - b := by
        intro h
        have hbeq : b = -b := by
          apply add_left_cancel (a := x)
          simpa [sub_eq_add_neg] using h
        have hbadd : b + b = b := hbb.trans hbeq.symm
        apply hb0
        apply add_right_cancel (b := b)
        simpa using hbadd
      refine {
        carrier := {x, x + b, x - b}
        avoids := ?_
        odd_card := ?_
        invariant := ?_ }
      · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
        refine ⟨?_, ?_, ?_⟩
        · exact hx0.symm
        · intro h
          apply hxnb
          exact eq_neg_of_add_eq_zero_left h.symm
        · intro h
          apply hxb
          exact sub_eq_zero.mp h.symm
      · have hcard : ({x, x + b, x - b} : Finset (Fq d)).card = 3 := by
          rw [Finset.card_insert_of_notMem]
          · rw [Finset.card_insert_of_notMem]
            · simp
            · simpa using hx_add_ne_sub
          · simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
            exact ⟨hx_add_ne_x.symm, hx_sub_ne_x.symm⟩
        rw [hcard]
        exact ⟨1, rfl⟩
      · intro y
        simp only [Finset.mem_insert, Finset.mem_singleton]
        constructor
        · rintro (rfl | rfl | rfl)
          · exact Or.inr (Or.inl hcycle0)
          · exact Or.inr (Or.inr hcycle1)
          · exact Or.inl hcycle2
        · intro hy
          rw [gsmul] at hy
          rcases hy with hy | hy | hy
          · exact Or.inr (Or.inr (by
              calc
                y = -b + (b + y) := by abel
                _ = -b + x := by rw [hy]
                _ = x - b := by abel))
          · exact Or.inl (by
              calc
                y = -b + (b + y) := by abel
                _ = -b + (x + b) := by rw [hy]
                _ = x := by abel)
          · exact Or.inr (Or.inl (by
              calc
                y = -b + (b + y) := by abel
                _ = -b + (x - b) := by rw [hy]
                _ = x + (-b - b) := by abel
                _ = x + b := by rw [char_three_neg_sub_self]))
  · let a : Fq d := g.right.1.1
    let b : Fq d := g.left.toAdd
    have ha1 : a ≠ 1 := by
      intro ha
      apply hright
      apply Subtype.ext
      apply Units.ext
      exact ha
    let x0 : Fq d := b / (1 - a)
    have hden : 1 - a ≠ 0 := sub_ne_zero.mpr ha1.symm
    have hfixed : g • x0 = x0 := by
      rw [Saxl.affine_smul_def, cq_smul_eq_mul]
      change b + a * (b / (1 - a)) = b / (1 - a)
      field_simp
      ring
    by_cases hx0 : x0 = 0
    · have hb0 : b = 0 := by
        simpa [x0, hden] using hx0
      refine {
        carrier := cqValueFinset d
        avoids := zero_not_mem_cqValueFinset d
        odd_card := odd_card_cqValueFinset d hd
        invariant := ?_ }
      intro y
      apply cqValueFinset_invariant_of_left_eq_zero d g
      exact hb0
    · refine {
        carrier := {x0}
        avoids := by simpa [eq_comm] using hx0
        odd_card := by simp
        invariant := ?_ }
      intro y
      simp only [Finset.mem_singleton]
      constructor
      · rintro rfl
        exact hfixed
      · intro hy
        apply (smul_left_cancel_iff g).mp
        rw [hy, hfixed]

end SaxlCounterexamples.EveryBase
end
