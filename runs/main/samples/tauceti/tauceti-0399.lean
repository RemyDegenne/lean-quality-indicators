public section

namespace TauCeti.HopfIdeal

universe u

variable {k : Type u} [Field k]

variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

theorem isMaximalTorus_iff_exists_eq_conjugate [IsAlgClosed k]
    (D : HopfIdeal k H)
    (hD : IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) D)
    (I : HopfIdeal k H)
    (hcontain :
      DiagonalizableGroup.groupLikeSpannedProperty k
        (FiniteTypeCommHopfAlgCat.quotient
          ⟨_root_.CommHopfAlgCat.of k H, (finiteTypeCommHopfAlgProperty_iff _).2 inferInstance⟩
          I) →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I) :
    IsMaximalTorus k (_root_.CommHopfAlgCat.of k H) I ↔
      ∃ g : WithConv (H →ₐ[k] k), I = D.conjugate g := by
  constructor
  · intro hI
    have htorus := ((isMaximalTorus_iff k (_root_.CommHopfAlgCat.of k H) I).mp hI).1
    have hsplit := torusCommHopfAlgProperty.split k _ htorus
    exact exists_eq_conjugate_of_isMaximalTorus_of_split (k := k) (H := H)
      D hD hcontain hI hsplit
  · rintro ⟨g, rfl⟩
    exact hD.conjugate g

end TauCeti.HopfIdeal
end
