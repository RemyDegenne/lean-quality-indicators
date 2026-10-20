public section

namespace TauCeti

open scoped commutatorElement

attribute [local instance 2000] Ring.toAddCommGroup

variable {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {χ : G →ₜ* ℤ_[p]ˣ}

namespace IsCrossedHom

variable {f : G → ℤ_[p]} (hf : IsCrossedHom χ f) (hχ : ∀ g, χ g ∈ unitsPrincipal p 1)
  (hfc : Continuous f)

include hf hχ hfc

variable (k : ℕ)

theorem gradedFunctional_gradedPowIter_gradedMkZero {g : G} (hg : χ g = 1) :
    hf.gradedFunctional hχ hfc k (gradedPowIter p G k (gradedMkZero p G g)) =
      PadicInt.toZMod (f g) := by
  rw [gradedPowIter_gradedMkZero]
  exact hf.gradedFunctional_gradedMk hχ hfc k _ (by rw [hf.map_pow_of_eq_one hg, Nat.cast_pow])

end IsCrossedHom
end TauCeti
end
