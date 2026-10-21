namespace OAI

noncomputable section

open scoped BigOperators

namespace TotientAsymptotic

lemma prime_parts_injective {N n : ℕ} (hn : n ≤ N) :
    Function.Injective (fun p : Fin N → ℕ => (primeInitial p n hn,primeFinal p n)) := by
  intro p q he
  funext j
  by_cases hj : j.val < n
  · exact congrFun (congrArg Prod.fst he) ⟨j.val,hj⟩
  · have hh := congrFun (congrArg Prod.snd he) ⟨j.val-n,by have := j.isLt; omega⟩
    simpa only [primeFinal,Nat.add_sub_of_le (Nat.le_of_not_gt hj)] using hh

end TotientAsymptotic
end
end OAI
