public section

open Differential algebraMap IntermediateField Finset Polynomial

variable (F : Type*) (K : Type*) [Field F] [Field K] [Differential F] [Differential K]

variable [Algebra F K] [DifferentialAlgebra F K]

/--
We say that a differential field extension `K / F` is Liouville if, whenever an element `a ∈ F` can
be written as `a = v + ∑ cᵢ * logDeriv uᵢ` for `v, cᵢ, uᵢ ∈ K` and `cᵢ` constant, it can also be
written in that way with `v, cᵢ, uᵢ ∈ F`.
-/
class IsLiouville : Prop where
  isLiouville (a : F) (ι : Type) [Fintype ι] (c : ι → F) (hc : ∀ x, (c x)′ = 0)
    (u : ι → K) (v : K) (h : a = ∑ x, c x * logDeriv (u x) + v′) :
    ∃ (ι₀ : Type) (_ : Fintype ι₀) (c₀ : ι₀ → F) (_ : ∀ x, (c₀ x)′ = 0)
      (u₀ : ι₀ → F) (v₀ : F), a = ∑ x, c₀ x * logDeriv (u₀ x) + v₀′

end
