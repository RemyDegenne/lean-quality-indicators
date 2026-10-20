public section

namespace TauCeti.HopfIdeal

universe u v

section AlgClosed

variable {k : Type u} [Field k] [IsAlgClosed k]

variable {H : Type u} [CommRing H] [HopfAlgebra k H] [Algebra.FiniteType k H]

theorem exists_conjugate_eq_of_isBorelOverAlgClosed (D : HopfIdeal k H)
    (hD : IsBorelCandidate k (FiniteTypeCommHopfAlgCat.of k H) D)
    (hcontain : ∀ I : HopfIdeal k H, IsBorelOverAlgClosed k
      (FiniteTypeCommHopfAlgCat.of k H) I →
      ∃ g : WithConv (H →ₐ[k] k), D.conjugate g ≤ I)
    {I J : HopfIdeal k H}
    (hI : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) I)
    (hJ : IsBorelOverAlgClosed k (FiniteTypeCommHopfAlgCat.of k H) J) :
    ∃ g : WithConv (H →ₐ[k] k), I.conjugate g = J := by
  obtain ⟨g, rfl⟩ := (isBorelOverAlgClosed_iff_exists_eq_conjugate D hD hcontain I).mp hI
  obtain ⟨h, rfl⟩ := (isBorelOverAlgClosed_iff_exists_eq_conjugate D hD hcontain J).mp hJ
  exact ⟨h * g⁻¹, by simp [conjugate_mul]⟩

end AlgClosed
end TauCeti.HopfIdeal
end
