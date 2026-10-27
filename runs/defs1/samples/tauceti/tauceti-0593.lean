public section

open _root_.CommHopfAlgCat _root_.CommHopfAlgCat.Hom

open CategoryTheory

namespace TauCeti

universe u v w

namespace CommHopfAlgCat

variable {R : Type u} [CommRing R] {H K : _root_.CommHopfAlgCat.{v} R}

/-- The kernel Hopf ideal of a morphism of commutative Hopf algebras: the image of the
augmentation ideal of the source. It is an ideal of the *codomain* `K`, the coordinate
ring of the source of the induced group-scheme morphism `Spec K ⟶ Spec H`; its quotient
represents the kernel of that morphism. -/
noncomputable def kernelHopfIdeal (f : H ⟶ K) : HopfIdeal R K :=
  (HopfIdeal.augmentation R H).map f.hom

end CommHopfAlgCat
end TauCeti
end
