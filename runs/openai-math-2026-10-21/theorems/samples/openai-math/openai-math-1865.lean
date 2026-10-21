namespace OAI

namespace MatroidProphet

open Finset

variable {α : Type*} [Fintype α] [DecidableEq α]

attribute [local instance] Classical.propDecidable

theorem safeBirth_probability (M : Matroid α) (hE : M.E = Set.univ)
    (κ : ℕ) (D : ℕ → Set α) (G : ℕ → Finset α)
    (hG : Pairwise (fun i j => Disjoint (G i) (G j))) (q : α → ℝ)
    (hq0 : ∀ e, 0 ≤ q e) (hq1 : ∀ e, q e ≤ 1)
    (h : ℕ) (d : α) (hd : d ∉ M.closure ∅) (m : ℕ) (hb : activation h + 2 ≤ -(m:ℤ)) :
    bitsExpectation q univ (fun C =>
      if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
          (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0) ≤
    bitsExpectation q univ (fun C => bitsExpectation q univ (fun T =>
      if safeBirthEvent M hE κ D G h d (-(m:ℤ)) C T then 1 else 0)) := by
  let P := reversePrefixTree M hE κ D G h m (-1) (fun _ => Set.univ)
  have hP (C : Finset α) (j : ℕ) (hj : j ≤ h) : P.run C j =
      nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ)) :=
    reversePrefixTree_from_univ_path M hE κ D G h hG m C hj
  have hid := reverseDoubleExit_after_prefix M hE κ D G h d hG q m (-1) (fun _ => Set.univ)
    (reverseClosed_univ M hE κ D (-1)) (-(m:ℤ)-1)
  have heq : bitsExpectation q univ (fun C =>
      if d ∈ nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) h (-(m:ℤ)) then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1)
          (fun j => nominalPath M hE κ D (fun i => (C : Set α) ∩ (G i : Set α)) j (-(m:ℤ))))^2 else 0) =
      bitsExpectation q univ (fun C => if d ∈ P.run C h then
        (reverseHazard M hE κ D G q d h (-(m:ℤ)-1) (P.run C))^2 else 0) := by
    apply bitsExpectation_congr
    intro C hC
    rw [hP C h le_rfl, reverseHazard_state_congr M hE κ D (P.run C) _ G q _ h d
      (fun j hj => hP C j hj.le)]
  rw [heq, ← hid]
  apply bitsExpectation_mono q hq0 hq1
  intro C hC
  apply bitsExpectation_mono q hq0 hq1
  intro T hT
  exact doubleExit_le_safeBirth M hE κ D (P.run C) G C T (-(m:ℤ)) h d hd (hP C) (by omega)

end MatroidProphet
end OAI
