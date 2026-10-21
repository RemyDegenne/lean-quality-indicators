namespace OAI

noncomputable section

open scoped Topology

open scoped BigOperators ContDiff

open scoped BigOperators ContDiff

open Nat.Partrec (Code)

open scoped BigOperators ContDiff

open Nat.Partrec (Code)

open scoped BigOperators ContDiff

open Nat.Partrec (Code)

namespace BoxTransport.Routing.Computation

@[fun_prop] theorem pr_node {α} [Primcodable α] {m : α → ℕ} {e : α → Expr}
    (hm : Primrec m) (he : Primrec e) : Primrec (fun a => node (m a) (e a)) := primrec_node.comp (hm.pair he)

end BoxTransport.Routing.Computation
end
end OAI
