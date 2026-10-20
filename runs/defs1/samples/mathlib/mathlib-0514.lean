@[expose] public section

universe u

open Filter Function Order Set

open Topology

variable {ι α β γ : Type*} [TopologicalSpace α] [TopologicalSpace β] [TopologicalSpace γ]

namespace TopologicalSpace

namespace Opens

/-- A version of `Set.inclusion` not requiring definitional abuse -/
abbrev inclusion {U V : Opens α} (h : U ≤ V) : U → V := Set.inclusion h

end Opens
end TopologicalSpace
end
