public section

noncomputable section

open CategoryTheory Limits Set Topology Topology.RelCWComplex

universe v u

namespace TauCeti.ComplexProjectiveSpace

attribute [local instance] cwComplex Abelian.hasFiniteBiproducts

variable {n : ℕ} {A : Type u} [Category.{v} A] [HasCoproducts.{0} A] [Abelian A] (R : A)

local notation "K" => cellularChainComplex (univ : Set (ComplexProjectiveSpace n)) R

theorem isZero_singularHomology_of_odd {k : ℕ} (hk : Odd k) :
    IsZero (((AlgebraicTopology.singularHomologyFunctor A k).obj R).obj
      (TopCat.of (ComplexProjectiveSpace n))) :=
  (isZero_X_of_odd R hk).of_iso (singularHomologyIsoX R k)

end TauCeti.ComplexProjectiveSpace
end
end
