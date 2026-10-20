public section

namespace TauCeti.QuadraticMap.OrthogonalCompactOpens

open Filter

open _root_.QuadraticMap

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
  {Q : QuadraticForm ℚ V} {Q' : QuadraticForm ℚ W}
  (U : OrthogonalCompactOpens Q) (U' : OrthogonalCompactOpens Q')
  (e : Q.IsometryEquiv Q')

section

variable [FiniteDimensional ℚ V] [FiniteDimensional ℚ W]

theorem map_range_finiteAdelicSpecialOrthogonalDiagonal_of_isometry
    (he : ∀ᶠ p in cofinite, Set.BijOn (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr
      (U.specialOrthogonal p) (U'.specialOrthogonal p)) :
    U.finiteAdelicSpecialOrthogonalDiagonal.range.map
        (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
          (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr) he :
          U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal) =
      U'.finiteAdelicSpecialOrthogonalDiagonal.range := by
  have hcomp :
      (restrictedProductCongrRight U.specialOrthogonal U'.specialOrthogonal
        (fun p : Nat.Primes ↦ (e.baseChange ℚ_[p]).specialOrthogonalGroupCongr) he :
          U.finiteAdelicSpecialOrthogonal →* U'.finiteAdelicSpecialOrthogonal).comp
          U.finiteAdelicSpecialOrthogonalDiagonal =
        U'.finiteAdelicSpecialOrthogonalDiagonal.comp
          (e.specialOrthogonalGroupCongr : _ →* _) :=
    MonoidHom.ext (U.restrictedProductCongrRight_finiteAdelicSpecialOrthogonalDiagonal U' e he)
  rw [MonoidHom.map_range, hcomp, MonoidHom.range_comp,
    MonoidHom.range_eq_top.mpr e.specialOrthogonalGroupCongr.surjective, ← MonoidHom.range_eq_map]

end
end TauCeti.QuadraticMap.OrthogonalCompactOpens
end
