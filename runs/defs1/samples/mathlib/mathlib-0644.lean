@[expose] public section

open Function

open scoped Finset

universe u v

variable {η α ι κ : Type*}

namespace Combinatorics

namespace Subspace

variable {η α ι κ : Type*} {l : Subspace η α ι} {x : η → α} {i : ι} {a : α} {e : η}

variable {η' α' ι' : Type*}

/-- Change the index types of a subspace. -/
def reindex (l : Subspace η α ι) (eη : η ≃ η') (eα : α ≃ α') (eι : ι ≃ ι') : Subspace η' α' ι' where
  idxFun i := (l.idxFun <| eι.symm i).map eα eη
  proper e := (eι.exists_congr fun i ↦ by cases h : idxFun l i <;>
    simp [*, Equiv.eq_symm_apply]).1 <| l.proper <| eη.symm e

end Subspace
end Combinatorics
end
