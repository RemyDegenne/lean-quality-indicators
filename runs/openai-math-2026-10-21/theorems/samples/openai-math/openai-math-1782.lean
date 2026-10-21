namespace OAI

noncomputable section

namespace LaughlinGap

open scoped BigOperators InnerProduct

lemma Antisymmetric.perm {N Q : ℕ} {ψ : State N Q} (hψ : Antisymmetric ψ)
    (a : Configuration N Q) (σ : Equiv.Perm (Fin N)) :
    ψ (a ∘ σ) = Equiv.Perm.sign σ • ψ a := by
  induction σ using Equiv.Perm.swap_induction_on' with
  | one => simp
  | mul_swap s i j hij ih => simp_all [← Function.comp_assoc, hψ i j hij]

end LaughlinGap
end
end OAI
