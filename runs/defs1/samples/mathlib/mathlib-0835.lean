public section

namespace Asymptotics

open Filter Function

open scoped Topology

section NormedAddCommGroup

variable {α β : Type*} [NormedAddCommGroup β]

variable {u v w : α → β} {l : Filter α}

/-- Two functions `u` and `v` are said to be asymptotically equivalent along a filter `l`
  (denoted as `u ~[l] v` in the `Asymptotics` namespace)
  when `u x - v x = o(v x)` as `x` converges along `l`. -/
@[expose] def IsEquivalent (l : Filter α) (u v : α → β) :=
  (u - v) =o[l] v

end NormedAddCommGroup
end Asymptotics
end
