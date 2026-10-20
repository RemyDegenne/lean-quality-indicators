public section

namespace TauCeti

open Matrix

theorem isModularEigenrow_dihedralGroupThreeCentralCharacterTable_zmod
    (i : DihedralGroupThreeClassIndex) :
    (dihedralClassData 3).IsModularEigenrow
      (fun j => (dihedralGroupThreeCentralCharacterTable i j :
        ZMod dihedralGroupThreeDixonPrimeData.p)) :=
  (isModularEigenrow_dihedralGroupThreeCentralCharacterTable_int i).map
    (Int.castRingHom (ZMod dihedralGroupThreeDixonPrimeData.p))

end TauCeti
end
