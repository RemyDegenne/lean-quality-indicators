namespace OAI

section

open scoped BigOperators Classical

open Finset

namespace SharpLogRamsey

namespace Foundation

variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)

theorem ramsey_has_property {s t : ℕ} (hs : 2 ≤ s) (ht : 1 ≤ t) :
    RamseyProperty s t (ramsey s t) := Nat.sInf_mem (ramseyProperty_nonempty hs ht)

end Foundation
end SharpLogRamsey
end
end OAI
