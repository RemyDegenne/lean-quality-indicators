set_option warningAsError true

@[expose] public section

namespace Steinberg

universe uι uR uG

open scoped commutatorElement

variable {ι : Type uι} {R : Type uR} [Ring R]

theorem lift_unique {G : Type uG} [Group G] (f : Root ι → R → G)
    (hadd hdisjoint hcomposable) (φ : Presented ι R →* G)
    (hφ : ∀ p a, φ (generator p a) = f p a) :
    φ = lift f hadd hdisjoint hcomposable := by
  apply hom_ext
  intro p a
  rw [hφ, lift_generator]

end Steinberg
end
