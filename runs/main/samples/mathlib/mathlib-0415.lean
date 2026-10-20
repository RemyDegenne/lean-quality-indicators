@[expose] public section

open Multiset Subtype Function

universe u

variable {α : Type*} {β : Type*}

namespace Finset

attribute [local trans] Subset.trans Superset.trans

section Cons

variable {s t : Finset α} {a b : α}

@[simp]
theorem mk_cons {s : Multiset α} (h : (a ::ₘ s).Nodup) :
    (⟨a ::ₘ s, h⟩ : Finset α) = cons a ⟨s, (nodup_cons.1 h).2⟩ (nodup_cons.1 h).1 :=
  rfl

end Cons
end Finset
end
