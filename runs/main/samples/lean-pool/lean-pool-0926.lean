@[expose] public section

namespace PDL

namespace LoadedCluster

variable {X : Sequent} {tab : Tableau .nil X} {C : LoadedCluster tab}
  {θ : FinePathIn tab → Formula} {x : List Nat}

lemma rho_eq_of_typ_label {n m} {y : List Nat} (hx : C.Q.atOpt x = some n)
    (hy : C.Q.atOpt y = some m) (htyp : n.typ = m.typ) (hlab : n.label = m.label) :
    C.rho x = C.rho y := by
  rw [rho_of_atOpt hx, rho_of_atOpt hy, regionOf, regionOf, htyp, hlab]

end LoadedCluster
end PDL
end
