set_option warningAsError true

@[expose] public section

namespace Steinberg

universe uι uR uG

open scoped commutatorElement

variable {ι : Type uι} {R : Type uR} [Ring R]

theorem generator_commutator (i j k : ι)
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) (a b : R) :
    ⁅generator (root i j hij) a, generator (root j k hjk) b⁆ =
      generator (root i k hik) (a * b) := by
  have h := PresentedGroup.one_of_mem (rels := relations (ι := ι) (R := R))
    (show ⁅word (root i j hij) a, word (root j k hjk) b⁆ *
      (word (root i k hik) (a * b))⁻¹ ∈ relations from
      Or.inr (Or.inr ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩))
  change ⁅generator (root i j hij) a, generator (root j k hjk) b⁆ *
    (generator (root i k hik) (a * b))⁻¹ = 1 at h
  exact eq_of_mul_inv_eq_one h

end Steinberg
end
