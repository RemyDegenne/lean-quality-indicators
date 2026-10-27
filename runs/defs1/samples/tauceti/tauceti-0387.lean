public section

namespace TauCeti.DynkinType

open RootPairing.GeckConstruction Set

open scoped _root_.Matrix

noncomputable section

attribute [local instance 100] LieRing.ofAssociativeRing

attribute [local instance] TauCeti.moduleNNRat

variable (t : DynkinType) (ht : t.Valid)

/-- **The integral orbit of the standard coordinates of the Geck module**: the `ℤ`-span of the
images of the standard coordinate vectors under the simple-generator Kostant form.

Every downstream consumer of a Kostant root subgroup takes a `ℤ`-submodule preserved by the whole
integral form as a hypothesis. This one is preserved by construction, by
`TauCeti.DynkinType.geckRepresentation_mem_geckOrbit`, and it is full by
`TauCeti.DynkinType.span_geckOrbit_eq_top`. Its finite generation over `ℤ` is proved in
`TauCeti/LinearAlgebra/RootSystem/SimplyConnectedRootDatum/GeckLattice/Basic.lean`,
where the orbit is identified with the coordinate lattice. -/
def geckOrbit : Submodule ℤ (t.GeckIndex ht → ℚ) :=
  Subring.orbitOfRep (t.kostantForm ht) (t.geckRepresentation ht)
    (range fun x => Pi.single x 1)

end
end TauCeti.DynkinType
end
