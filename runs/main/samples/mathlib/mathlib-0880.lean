@[expose] public noncomputable section

open Function

open Finsupp hiding single mapDomain

variable {ι F R S T M N O : Type*}

namespace MonoidAlgebra

section Semiring

variable [Semiring R] [Semiring S] [Semiring T] {f : M → N} {a : M} {r : R}

@[to_additive]
lemma range_map (f : R →+ S) : Set.range (map (M := M) f) = {x | ∀ i, x.coeff i ∈ Set.range f} :=
  calc
    _ = coeffEquiv ⁻¹' (Set.range (mapRange f (map_zero f) ∘ coeffEquiv)) := by
      simp_rw [comp_def, Equiv.eq_preimage_iff_image_eq, ← Set.range_comp', coeffEquiv_apply,
        coeff_map]
    _ = _ := by simp [Finsupp.range_mapRange]

end Semiring
end MonoidAlgebra
end
