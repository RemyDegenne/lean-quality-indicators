namespace OAI

noncomputable section

namespace Dixmier

namespace Masked

open Finset

open scoped ComplexConjugate

variable {G I K : Type*} [Group G] [Fintype I] [Fintype K]

local instance : DecidableEq I := Classical.decEq I

local instance : DecidableEq G := Classical.decEq G

local instance : DecidableEq ℂ := Classical.decEq ℂ

theorem basis_inner_right (v : Fibre K) (b : K) :
    inner ℂ v (EuclideanSpace.basisFun K ℂ b) = conj (v b) := by
  rw [← EuclideanSpace.basisFun_inner K ℂ v b, inner_conj_symm]

end Masked
end Dixmier
end
end OAI
