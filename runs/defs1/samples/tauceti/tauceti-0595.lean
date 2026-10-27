public section

namespace TauCeti

open CategoryTheory CategoryTheory.Limits

universe u v w

section ArrowHom

variable (k : Type u) {Q : Type v} [Field k] [Quiver.{w} Q]

/-- **The morphism of an arrow**: for `e : i ⟶ j`, the morphism `Pⱼ ⟶ Pᵢ` prefixing `e` to every
path out of `j`. Under the universal property of `Pⱼ` it is the element `e` of `(Pᵢ)ⱼ`. -/
noncomputable def indecProjRepArrowHom {i j : Q} (e : i ⟶ j) :
    indecProjRep k Q j ⟶ indecProjRep k Q i :=
  indecProjRepHom j (indecProjRep k Q i) (indecProjRepBasis k i j e.toPath)

end ArrowHom
end TauCeti
end
