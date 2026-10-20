public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe v w

variable (k : Type (max v w)) {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **The canonical surjection `Pᵢ ↠ Sᵢ`**: under the universal property of `Pᵢ` it is the
generator of the line `(Sᵢ)ᵢ`. It sends the basis vector of the trivial path to that generator and
kills the basis vector of every path of positive length. -/
noncomputable def indecProjRepToSimpleRep (i : Q) : indecProjRep k Q i ⟶ simpleRep k Q i :=
  indecProjRepHom i (simpleRep k Q i) (simpleRepGenerator k i)

end TauCeti
end
