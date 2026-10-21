namespace OAI

namespace CubeShuffle

lemma centralFactor_zero (L : ℕ) (E : Finset (Card 0)) (a : ℝ) :
    centralFactor L 0 E a =
      if (fun j => Fin.elim0 j : Card 0) ∈ E then 1 else (Nat.factorial (2^L):ℝ)^(-a) := by
  classical
  let z : Card 0 := fun j => Fin.elim0 j
  have he : (E.card:ℝ) = if z ∈ E then 1 else 0 := by
    by_cases hz : z ∈ E
    · have he : E = {z} := by
        ext u
        rw [Subsingleton.elim u z]
        simp only [hz,Finset.mem_singleton]
      rw [he,ite_eq_left (by simpa only [he] using hz),Finset.card_singleton,Nat.cast_one]
    · have he : E = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (fun u hu => hz (Subsingleton.elim u z ▸ hu))
      rw [he,Finset.card_empty,Nat.cast_zero,ite_eq_right (by simp)]
  unfold centralFactor
  rw [pow_zero,he]
  split_ifs <;> simp

end CubeShuffle
end OAI
