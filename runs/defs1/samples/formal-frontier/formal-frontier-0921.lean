set_option warningAsError true

@[expose] public section

namespace Steinberg

universe uι uR uG

open scoped commutatorElement

variable {ι : Type uι} {R : Type uR} [Ring R]

/-- Extend any family satisfying exactly these three laws to a group homomorphism. -/
def lift {G : Type uG} [Group G] (f : Root ι → R → G)
    (hadd : ∀ p a b, f p a * f p b = f p (a + b))
    (hdisjoint : ∀ i j k l (hij : i ≠ j) (hkl : k ≠ l)
      (_hjk : j ≠ k) (_hli : l ≠ i) (a b : R),
      ⁅f (root i j hij) a, f (root k l hkl) b⁆ = 1)
    (hcomposable : ∀ i j k (hij : i ≠ j) (hjk : j ≠ k)
      (hik : i ≠ k) (a b : R),
      ⁅f (root i j hij) a, f (root j k hjk) b⁆ = f (root i k hik) (a * b)) :
    Presented ι R →* G :=
  PresentedGroup.toGroup (f := fun gen => f gen.1 gen.2) (by
    intro w hw
    rcases hw with ⟨p, a, b, rfl⟩ | ⟨i, j, k, l, hij, hkl, hjk, hli, a, b, rfl⟩ |
        ⟨i, j, k, hij, hjk, hik, a, b, rfl⟩
    · simp only [word, map_mul, map_inv, FreeGroup.lift_apply_of, hadd, mul_inv_cancel]
    · simpa only [word, map_commutatorElement, FreeGroup.lift_apply_of] using
        hdisjoint i j k l hij hkl hjk hli a b
    · simp only [word, map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of]
      rw [hcomposable i j k hij hjk hik a b, mul_inv_cancel])

end Steinberg
end
