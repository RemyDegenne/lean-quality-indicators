@[expose] public section

universe u v w uR uτ uσ uL uK

namespace MvPolynomial

theorem X_mem_range_fractionRing_map_finset_iff
    {R : Type uR} [CommRing R] [IsDomain R] {σ : Type uσ}
    {K : Type uK} [CommRing K] [Algebra (MvPolynomial σ R) K]
    [IsFractionRing (MvPolynomial σ R) K] (S : Finset σ) (i : σ) :
    algebraMap (MvPolynomial σ R) K (X i) ∈
      Set.range
        (IsFractionRing.map
          (A := MvPolynomial {j : σ // j ∈ S} R) (B := MvPolynomial σ R)
          (K := FractionRing (MvPolynomial {j : σ // j ∈ S} R)) (L := K)
          (j := (rename (R := R) Subtype.val).toRingHom)
          (rename_injective Subtype.val Subtype.val_injective)) ↔
      i ∈ S := by
  simpa only [Subtype.range_val_subtype, Set.mem_ofPred_eq] using
    (X_mem_range_fractionRing_map_rename_iff
      (R := R) (L := FractionRing (MvPolynomial {j : σ // j ∈ S} R)) (K := K)
      (Subtype.val : {j : σ // j ∈ S} → σ) Subtype.val_injective i)

end MvPolynomial
end
