@[expose] public section

universe v v' u u'

namespace CategoryTheory

open Category Limits ZeroObject MorphismProperty

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]

namespace ObjectProperty

variable (P : ObjectProperty C)

/-- The class of isomorphisms modulo a Serre class: given a
Serre class `P : ObjectProperty C`, this is the class of morphisms `f`
such that `kernel f` and `cokernel f` satisfy `P`. -/
@[nolint unusedArguments]
def isoModSerre [P.IsSerreClass] : MorphismProperty C :=
  P.monoModSerre ⊓ P.epiModSerre

end ObjectProperty
end CategoryTheory
end
