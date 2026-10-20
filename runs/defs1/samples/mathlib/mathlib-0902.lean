@[expose] public section

universe w v u

open CategoryTheory TopologicalSpace Opposite Functor

variable (C : Type u) [Category.{v} C]

namespace TopCat

variable {C}

namespace Presheaf

macro "sheaf_restrict" : attr =>
  `(attr|aesop safe 50 apply (rule_sets := [$(Lean.mkIdent `Restrict):ident]))

macro (name := restrict_tac) "restrict_tac" c:Aesop.tactic_clause* : tactic =>
`(tactic| first | assumption |
  aesop $c*
    (config := { terminal := true
                 assumptionTransparency := .reducible
                 enableSimp := false })
    (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

macro (name := restrict_tac?) "restrict_tac?" c:Aesop.tactic_clause* : tactic =>
`(tactic|
  aesop? $c*
    (config := { terminal := true
                 assumptionTransparency := .reducible
                 enableSimp := false
                 maxRuleApplications := 300 })
  (rule_sets := [-default, -builtin, $(Lean.mkIdent `Restrict):ident]))

variable {X : TopCat.{w}} {C : Type u} [Category.{v} C] {FC : C → C → Type*} {CC : C → Type*}

variable [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]

scoped[AlgebraicGeometry] infixl:80 " |_ₕ " => TopCat.Presheaf.restrict

scoped[AlgebraicGeometry] notation:80 x " |_ₗ " U " ⟪" e "⟫ " =>
  @TopCat.Presheaf.restrict _ _ _ _ _ _ _ _ _ x U (@homOfLE (Opens _) _ U _ e)

open AlgebraicGeometry

scoped[AlgebraicGeometry] infixl:80 " |_ " => TopCat.Presheaf.restrictOpen

open CategoryTheory.Limits

variable (C)

scoped[AlgebraicGeometry] notation f:80 " _* " P:81 =>
  Functor.obj (TopCat.Presheaf.pushforward _ f) P

variable {C}

variable (C)

variable [HasColimits C]

noncomputable section

/-- Pulling back along a homeomorphism is the same as pushing forward along its inverse. -/
def pullbackHomIsoPushforwardInv {X Y : TopCat.{v}} (H : X ≅ Y) :
    pullback C H.hom ≅ pushforward C H.inv :=
  Adjunction.leftAdjointUniq (pullbackPushforwardAdjunction C H.hom)
    (presheafEquivOfIso C H.symm).toAdjunction

end
end Presheaf
end TopCat
end
