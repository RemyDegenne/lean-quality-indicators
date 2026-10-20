public section

open CategoryTheory Opposite Set TopologicalSpace TauCeti.AlgebraicGeometry

universe u

noncomputable section

namespace AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}} [IrreducibleSpace X]

/-- The rational function represented by a local section of a sheaf of modules after choosing a
free rank-one trivialization on a dense open subset. -/
def rationalFunction (M : X.Modules) {U : X.Opens}
    (e : SheafOfModules.free (R := X.ringCatSheaf.over U) PUnit ≅ M.over U)
    (hU : Dense (U : Set X)) (V : X.Opens) [Nonempty V] :
    Γ(M, V) →+ X.functionField := by
  let W : X.Opens := V ⊓ U
  let _ : Nonempty W := Opens.nonempty_coeSort.mpr
    (hU.inter_open_nonempty V V.isOpen (Opens.nonempty_coeSort.mp ‹_›))
  let A : Over U := Over.mk (homOfLE (show W ≤ U from inf_le_right))
  exact (X.germToFunctionField W).hom.toAddMonoidHom.comp
    (((trivializationCoordinateIso M e).hom.val.app (op A)).hom.toAddMonoidHom.comp
      (M.presheaf.map (homOfLE inf_le_left).op).hom)

end AlgebraicGeometry.Scheme.Modules
end
end
