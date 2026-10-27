public section

set_option warningAsError true

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

noncomputable section

universe v u

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{v} C]

namespace AcyclicResolution

variable {A X X' : C} (I : InjectiveResolution A) (g : X' ⟶ X)

/-- Precomposition on Ext, with the source and target functors exposed in a
form convenient for exact cokernel constructions. -/
noncomputable abbrev extSourceMap (n : ℕ) (Y : C) :
    (extFunctorObj X n).obj Y ⟶ (extFunctorObj X' n).obj Y :=
  ((extFunctor n).map g.op).app Y

end AcyclicResolution
end CategoryTheory.Abelian.Ext
end
end
