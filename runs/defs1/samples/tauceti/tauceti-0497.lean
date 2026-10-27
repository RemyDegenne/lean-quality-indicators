public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module Set

open scoped TensorProduct

noncomputable section

/-- The modular coordinate subspace spanned by short root vectors and the two short simple
coroots. It is a Lie ideal; see `f4ShortRootLieIdeal`. -/
def f4ShortRootSubspace : Submodule (ZMod 2) f4ModularChevalleyLieAlgebra :=
  Submodule.span (ZMod 2) (f4ModularChevalleyBasis '' f4ShortChevalleyIndices)

end
end TauCeti.DynkinType
end
