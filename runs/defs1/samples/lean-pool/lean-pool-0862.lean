@[expose] public section

open scoped TensorProduct

namespace CK

variable (k : Type*) [CommRing k]

/-- A forest as an `H`-basis element, with the index forced to `FreeMonoid RTree`
    via `ofList` (so it is always typed `H k`, even on the empty forest). -/
noncomputable def _root_.CK.sf (r : Forest) : H k := MonoidAlgebra.single (FreeMonoid.ofList r) 1

end CK
end
