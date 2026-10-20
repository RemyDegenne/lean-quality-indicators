public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory

namespace TauCeti.CommHopfAlgCat

universe u v

variable {k : Type u} [Field k]

section Scheme

open AlgebraicGeometry

/-- The center of an affine group scheme, bundled as a commutative group scheme. -/
noncomputable def centerCommGroupScheme (H : _root_.CommHopfAlgCat.{u} k) :
    CommGrp (Over (Spec (CommRingCat.of k))) :=
  CommGrp.mk (centerGroupScheme H).X

end Scheme
end TauCeti.CommHopfAlgCat
end
