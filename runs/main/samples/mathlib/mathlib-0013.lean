@[expose] public section

variable {F ι α β γ : Type*} (f : α → β → β) (op : α → α → α)

namespace Finset

variable [Monoid β] [Monoid γ]

open scoped Function

variable [FunLike F β γ]

theorem noncommProd_erase_mul [DecidableEq α] (s : Finset α) {a : α} (h : a ∈ s) (f : α → β) (comm)
    (comm' := fun _ hx _ hy hxy ↦ comm (s.mem_of_mem_erase hx) (s.mem_of_mem_erase hy) hxy) :
    (s.erase a).noncommProd f comm' * f a = s.noncommProd f comm := by
  classical
  simpa only [← Multiset.map_erase_of_mem _ _ h] using!
    Multiset.noncommProd_erase_mul (s.1.map f) (Multiset.mem_map_of_mem f h) _

end Finset
end
