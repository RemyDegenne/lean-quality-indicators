public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule Module

open scoped TensorProduct

noncomputable section

/-- The root-vector--simple-coroot basis of the integral F₄ Chevalley lattice. -/
noncomputable def f4ChevalleyBasis :
    Basis f4ChevalleyIndex ℤ f4ChevalleyLieLattice :=
  f4ChevalleyRootVector_isChevalleySystem.rootSimpleCorootBasis f4KillingBase

end
end TauCeti.DynkinType
end
