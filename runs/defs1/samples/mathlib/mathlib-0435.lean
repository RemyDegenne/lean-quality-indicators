@[expose] public section

universe v u

namespace CategoryTheory

scoped notation "𝟙" => CategoryStruct.id

scoped infixr:80 " ≫ " => CategoryStruct.comp

syntax (name := sorryIfSorry) "sorry_if_sorry" : tactic

macro (name := rfl_cat) "rfl_cat" : tactic => do `(tactic| (refine id ?_; intros; apply_rfl))

macro (name := aesop_cat) "aesop_cat" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry | rfl_cat |
  aesop $c* (config := { introsTransparency? := some .default, terminal := true })
            (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

macro (name := aesop_cat?) "aesop_cat?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  first | sorry_if_sorry | try_this rfl_cat |
  aesop? $c* (config := { introsTransparency? := some .default, terminal := true })
             (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

macro (name := aesop_cat_nonterminal) "aesop_cat_nonterminal" c:Aesop.tactic_clause* : tactic =>
  `(tactic|
    aesop $c* (config := { introsTransparency? := some .default, warnOnNonterminal := false })
              (rule_sets := [$(Lean.mkIdent `CategoryTheory):ident]))

@[inherit_doc categoryTheoryDischarger]
elab (name := cat_disch) "cat_disch" : tactic =>
  categoryTheoryDischarger

set_option mathlib.tactic.category.grind true

/-- The typeclass `Category C` describes morphisms associated to objects of type `C`.
The universe levels of the objects and morphisms are unconstrained, and will often need to be
specified explicitly, as `Category.{v} C`. (See also `LargeCategory` and `SmallCategory`.) -/
-- After https://github.com/leanprover/lean4/pull/12286 and
-- https://github.com/leanprover/lean4/pull/12423, the morphism universe `v` would default to
-- being a universe output parameter.
-- See Note [universe output parameters and typeclass caching].
@[univ_out_params, pp_with_univ, stacks 0014, wikidata Q719395]
class Category (obj : Type u) : Type max u (v + 1) extends CategoryStruct.{v} obj where
  /-- Identity morphisms are left identities for composition. -/
  id_comp : ∀ {X Y : obj} (f : X ⟶ Y), 𝟙 X ≫ f = f := by cat_disch
  /-- Identity morphisms are right identities for composition. -/
  comp_id : ∀ {X Y : obj} (f : X ⟶ Y), f ≫ 𝟙 Y = f := by cat_disch
  /-- Composition in a category is associative. -/
  assoc : ∀ {W X Y Z : obj} (f : W ⟶ X) (g : X ⟶ Y) (h : Y ⟶ Z), (f ≫ g) ≫ h = f ≫ g ≫ h := by
    cat_disch

end CategoryTheory
end
