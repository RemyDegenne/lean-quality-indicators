@[expose] public section

noncomputable section

open Affine

open Set

open scoped Pointwise

namespace AffineSubspace

variable {k : Type*} {V : Type*} {P : Type*} [Ring k] [AddCommGroup V] [Module k V]
  [S : AffineSpace V P] {ι : Sort*}

variable (k V)

variable (P)

variable {k V P}

variable (k V) {p₁ p₂ : P}

variable (P)

variable {P}

variable (P)

variable {k V P}

@[simp]
theorem mk'_eq_mk'_iff {p q : P} {s : Submodule k V} :
    mk' p s = mk' q s ↔ p -ᵥ q ∈ s where
  mp h := by
    rw [AffineSubspace.ext_iff, Set.ext_iff] at h
    simpa using h p
  mpr h := ext_of_direction_eq (by simp) ⟨p, by simp, by simpa using h⟩

end AffineSubspace
end
end
