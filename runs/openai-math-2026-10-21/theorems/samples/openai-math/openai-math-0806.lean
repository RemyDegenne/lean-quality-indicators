namespace OAI

noncomputable section

namespace Generator

open scoped BigOperators

namespace MatrixUnitSystem

variable {ι A : Type*} [Fintype ι] [DecidableEq ι]

variable [Ring A] [StarRing A] [Algebra ℂ A]

variable (E : MatrixUnitSystem ι A)

variable [StarModule ℂ A]

open scoped BigOperators

variable {ι κ A : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

variable [Ring A] [StarRing A] [Algebra ℂ A] [StarModule ℂ A]

variable (E : MatrixUnitSystem ι A)

theorem algebra_le_iff (S : StarSubalgebra ℂ A) :
    E.algebra ≤ S ↔ ∀ i j, E.entry i j ∈ S := by
  constructor
  · exact fun h i j => h (E.entry_mem i j)
  · intro h x hx
    obtain ⟨a,rfl⟩ := (E.mem_algebra x).mp hx
    exact S.sum_mem fun i _ => S.sum_mem fun j _ => S.smul_mem (h i j) _

end MatrixUnitSystem
end Generator
end
end OAI
