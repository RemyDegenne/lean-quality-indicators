@[expose] public section

universe v u v' u'

open CategoryTheory Limits Functor

namespace CategoryTheory.Cat

/-- Any `T : Cat.{u, u}` with a unique object and discrete homs is isomorphic to `⊤_ Cat.{u, u}.` -/
noncomputable def terminalIsoOfUniqueOfIsDiscrete
    {T : Type u} [Category.{v} T] [Unique T] [IsDiscrete T] : ⊤_ Cat.{v, u} ≅ ↧T :=
  terminalIsoIsTerminal isTerminalOfUniqueOfIsDiscrete

end CategoryTheory.Cat
end
