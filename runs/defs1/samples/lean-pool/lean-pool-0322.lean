@[expose] public section

namespace MarkedGraphs

open Utilities

open Finset

namespace IndexedHarmonicCertificate

/-- Executable unit-index check, to be combined with `check` when the
certificate is intended to act on the ordinary source Laplacian. -/
def checkUnitIndexed (c : IndexedHarmonicCertificate G H) : Bool :=
  @decide (∀ p : G.V × G.V,
    c.edgeIndex p.1 p.2 = numEdges G p.1 p.2)
    Fintype.decidableForallFintype

end IndexedHarmonicCertificate
end MarkedGraphs
end
