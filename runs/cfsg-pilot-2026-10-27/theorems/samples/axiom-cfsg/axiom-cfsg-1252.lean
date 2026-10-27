public section

open scoped BigOperators Classical

namespace CFSG.Wreathed

open CFSG.TwoRankLowerBound.Helpers

variable {G : Type*} [Group G] [Fintype G]

theorem defect_normalizer_brauer_image_defect (basis : FiniteIrreducibleCharacterBasis G)
    (ideal : Ideal ComplexAlgebraicIntegers) [ideal.IsMaximal] (p : ℕ) [Fact p.Prime]
    [CharP (ComplexAlgebraicIntegers ⧸ ideal) p] (D : Subgroup G) (hD : IsPGroup p D)
    (localBasis : FiniteIrreducibleCharacterBasis (Subgroup.normalizer (D : Set G)))
    {θ : localBasis.index} {χ : basis.index}
    (hθ : coefficientBlockDefect localBasis ideal p θ
      (D.subgroupOf (Subgroup.normalizer (D : Set G))))
    (hχ : brauerNormalizerCharacterResidueHom ideal p D hD (Subgroup.normalizer (D : Set G))
      (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl localBasis θ =
        centralCharacterResidueHom basis ideal χ) :
    coefficientBlockDefect basis ideal p χ D := by
  have hvalue : ∀ Y : ConjClasses G, centralCharacterResidueHom basis ideal χ
      (centralConjugacyClassSum _ Y) = centralCharacterResidueHom localBasis ideal θ
        (centralNormalizerCoefficientProjection (localizedComplexIntegerRing ideal) D
          (Subgroup.normalizer (D : Set G)) (Subgroup.centralizer_le_normalizer (D : Set G)) le_rfl
          (centralConjugacyClassSum _ Y)) := fun Y => by
    rw [← hχ]
    rfl
  refine ⟨?_, fun Y U hYU hY => ?_⟩
  · obtain ⟨L, hL, hLres⟩ := hθ.1
    obtain ⟨x, hxL, hx⟩ := classDefect_normalizer_lift p D L hL
    refine ⟨ConjClasses.mk x.val, classDefectAt_classDefect hx, ?_⟩
    rw [hvalue, CFSG.Semidihedral.Principal.centralNormalizerCoefficientProjection_conjugacyClassSum
      _ p D x hx, hxL]
    exact hLres
  · apply (class_meets_centralizer_iff_subconjugate p D hD hYU).mp
    by_contra hnone
    apply hY
    rw [hvalue, brauerProjection_conjugacyClassSum_eq_zero _ D Y hnone, map_zero]

end CFSG.Wreathed
end
