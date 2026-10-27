public section

namespace CFSG.LieType.Chevalley.C2E6Std.MatrixModel

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Overlap
  CFSG.Monster.B.Classical.E6Adjoint

theorem toMat_ofFn (f : ℕ → Native.Vec) (k l : Fin 78) :
    toMat ((List.range 78).toArray.map f) k l = vecOf (f l) k := by
  simp [toMat, Array.getD_eq_getD_getElem?]

end CFSG.LieType.Chevalley.C2E6Std.MatrixModel
end
