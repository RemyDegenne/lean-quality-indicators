@[expose] public section

open scoped WithZero

universe u v w z

namespace MvPolynomial

variable {σ : Type u} {τ : Type v}

variable {k : Type w} {l : Type z} [Field k] [Field l]

local notation3 "ratio[" F "," U "," pivot "](" j ")" =>
  (algebraMap (MvPolynomial (WeightOneCoefficientVariables U pivot) F)
    (WeightOneCoefficientField F U pivot) (X (Sum.inr j)))

local notation3 "unweighted[" F "," U "," pivot "](" j ")" =>
  (algebraMap (MvPolynomial (WeightOneCoefficientVariables U pivot) F)
    (WeightOneCoefficientField F U pivot) (X (Sum.inl j)))

theorem weightOneResidueEquiv_map_changePivot (g : k →+* l) (e : σ ↪ τ)
    (S : Set σ) (T : Set τ) (h : ∀ j : σ, e j ∈ T ↔ j ∈ S)
    (i : S) (t : T)
    (r : IsLocalRing.ResidueField (WeightOneValuationRing (k := k) S i)) :
    weightOneResidueEquiv T t (weightOneResidueMap g e S T h i t r) =
      weightOneCoefficientChangePivot (l := l) T
        (weightOneAlignedPivot e S T h i) t
        (weightOneCoefficientFieldMap g e S T h i (weightOneResidueEquiv S i r)) := by
  let aligned := weightOneAlignedPivot e S T h i
  let cast := weightOneValuationRingEquiv (l := l) T aligned t
  have hres : weightOneResidueMap g e S T h i t r =
      IsLocalRing.ResidueField.mapEquiv cast
        (weightOneResidueMap g e S T h i aligned r) := by
    obtain ⟨a, rfl⟩ := IsLocalRing.residue_surjective r
    have hcompat : weightOneValuationRingMap g e S T h i t a =
        cast (weightOneValuationRingMap g e S T h i aligned a) := by
      apply Subtype.ext
      change weightOneFractionMap g e (a : FractionRing (MvPolynomial σ k)) =
        (((cast (weightOneValuationRingMap g e S T h i aligned a) :
          WeightOneValuationRing (k := l) T t)) : FractionRing (MvPolynomial τ l))
      rw [weightOneValuationRingEquiv_val]
      rfl
    simpa only [weightOneResidueMap_residue,
      IsLocalRing.ResidueField.mapEquiv_apply, IsLocalRing.ResidueField.map_residue,
      RingEquiv.coe_toRingHom] using
      congrArg (IsLocalRing.residue (WeightOneValuationRing (k := l) T t)) hcompat
  rw [hres, ← weightOneResidueEquiv_map g e S T h i r]
  simp only [weightOneCoefficientChangePivot, RingEquiv.trans_apply]
  change weightOneResidueEquiv T t
      (IsLocalRing.ResidueField.mapEquiv cast
        (weightOneResidueMap g e S T h i aligned r)) =
    weightOneResidueEquiv T t
      (IsLocalRing.ResidueField.mapEquiv cast
        ((weightOneResidueEquiv T aligned).symm
          (weightOneResidueEquiv T aligned
            (weightOneResidueMap g e S T h i aligned r))))
  rw [RingEquiv.symm_apply_apply]

end MvPolynomial
end
