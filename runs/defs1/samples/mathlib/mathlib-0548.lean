@[expose] public section

namespace List

namespace Pi

variable {ι : Type*} [DecidableEq ι] {α : ι → Sort*}

variable {i : ι} {l : List ι}

/-- Given `f` a function whose domain is `i :: l`, produce a function whose domain
is restricted to `l`. -/
def tail (f : ∀ j ∈ i :: l, α j) : ∀ j ∈ l, α j :=
  fun j hj ↦ f j (mem_cons_of_mem _ hj)

end Pi
end List
end
