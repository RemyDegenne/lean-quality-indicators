namespace OAI

namespace MatchingFPRAS.BitArithmetic

open Finset

lemma FractionBound.prod {ι : Type*} (A : Finset ι) (f : ι → ℝ) (B : ℕ)
    (h : ∀ i∈A,FractionBound B (f i)) : FractionBound (B^A.card) (∏ i∈A,f i) := by
  classical
  induction A using Finset.induction_on with
  | empty => simpa using FractionBound.one (B:=1) le_rfl
  | @insert i A hi ih =>
    simpa [prod_insert hi,card_insert_of_notMem hi,pow_succ,Nat.mul_comm] using
      (h i (mem_insert_self _ _)).mul (ih (fun j hj=>h j (mem_insert_of_mem hj)))

end MatchingFPRAS.BitArithmetic
end OAI
