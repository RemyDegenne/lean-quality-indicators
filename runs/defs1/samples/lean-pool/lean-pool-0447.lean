@[expose] public section

namespace ACMax

variable {V : Type*} [Fintype V]

open Classical in
/-- The **bad neighbours** of an apex `t` against a cherry: neighbours of degree `≥ 5`
or touching the cherry — the vertices that block the SingleVertex pair selection. -/
noncomputable def badApexNbrs (G : SimpleGraph V) (x z y t : V) : Finset V :=
  (G.neighborFinset t).filter (fun w => 5 ≤ G.degree w ∨ w ∈ cherryHubs G x z y)

end ACMax
end
