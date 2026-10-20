public section

namespace TauCeti

namespace GridRectanglePentagonDecomposition

variable {n : ℕ} {a s : Fin n} {x z : GridState n}

@[simp]
theorem recutRightEqRightSecond_inj
    (D E : GridRectanglePentagonDecomposition a s x z)
    (hcommonD : D.rectangle.right = D.pentagon.right)
    (hcommonE : E.rectangle.right = E.pentagon.right)
    (honeD : D.toRectangleDecomposition.HasOneCommonSide)
    (honeE : E.toRectangleDecomposition.HasOneCommonSide)
    (hrectangleD : D.rectangle.IsEmpty) (hpentagonD : D.pentagon.IsEmpty)
    (hrectangleE : E.rectangle.IsEmpty) (hpentagonE : E.pentagon.IsEmpty)
    (hsecondD : (D.recutOfIsEmpty honeD hrectangleD hpentagonD).second.right =
      D.pentagon.right)
    (hsecondE : (E.recutOfIsEmpty honeE hrectangleE hpentagonE).second.right =
      E.pentagon.right) :
    D.recutRightEqRightSecond hcommonD honeD hrectangleD hpentagonD hsecondD =
        E.recutRightEqRightSecond hcommonE honeE hrectangleE hpentagonE hsecondE ↔ D = E := by
  constructor
  · intro h
    have hD := D.isRecut_recutRightEqRightSecond
      hcommonD honeD hrectangleD hpentagonD hsecondD
    have hE := E.isRecut_recutRightEqRightSecond
      hcommonE honeE hrectangleE hpentagonE hsecondE
    rw [← h] at hE
    have hfirstD : D.toRectangleDecomposition.first.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_first_toGridRectangle] using hrectangleD
    have hlastD : D.toRectangleDecomposition.second.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle]
        using hpentagonD
    have hfirstE : E.toRectangleDecomposition.first.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_first_toGridRectangle] using hrectangleE
    have hlastE : E.toRectangleDecomposition.second.IsEmpty := by
      simpa only [GridRectangleBetween.isEmpty_iff_toGridRectangle_isEmptyFor,
        toRectangleDecomposition_middle, toRectangleDecomposition_second_toGridRectangle]
        using hpentagonE
    have hbackD := hD.symm honeD hfirstD hlastD
    have hbackE := hE.symm honeE hfirstE hlastE
    have hone := GridRectangleDecomposition.hasOneCommonSide_of_isRecut hbackD
      (D.toRectangleDecomposition.target_ne_source_of_hasOneCommonSide honeD)
    apply toRectangleDecomposition_injective
    exact (GridRectangleDecomposition.existsUnique_isRecut _ hone
      hD.isEmpty_first hD.isEmpty_second).unique hbackD hbackE
  · rintro rfl
    rfl

end GridRectanglePentagonDecomposition
end TauCeti
end
