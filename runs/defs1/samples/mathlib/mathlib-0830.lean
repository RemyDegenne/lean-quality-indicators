@[expose] public section

open List

universe u v

variable {ι : Type u} {α : ι → Type v} {i j : ι} {l : List ι}

namespace List

namespace TProd

variable [DecidableEq ι]

/-- Pi-types are equivalent to iterated products. -/
def piEquivTProd (hnd : l.Nodup) (h : ∀ i, i ∈ l) : (∀ i, α i) ≃ TProd α l :=
  ⟨TProd.mk l, TProd.elim' h, fun f => funext fun i => elim_mk l f (h i), mk_elim hnd h⟩

end TProd
end List
end
