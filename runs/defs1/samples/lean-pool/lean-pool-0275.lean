@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [Zero V] [One V] [Add V] [Mul V] [LT V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

section «lp_section_1»

namespace Negation

/-- Imported declaration from the Incompleteness formalization. -/
def blueprint (pL : LDef) : Language.UformulaRec1.Blueprint pL where
  rel := .mkSigma “y param k R v. !qqNRelDef y k R v” (by simp)
  nrel := .mkSigma “y param k R v. !qqRelDef y k R v” (by simp)
  verum := .mkSigma “y param. !qqFalsumDef y” (by simp)
  falsum := .mkSigma “y param. !qqVerumDef y” (by simp)
  and := .mkSigma “y param p₁ p₂ y₁ y₂. !qqOrDef y y₁ y₂” (by simp)
  or := .mkSigma “y param p₁ p₂ y₁ y₂. !qqAndDef y y₁ y₂” (by simp)
  all := .mkSigma “y param p₁ y₁. !qqExDef y y₁” (by simp)
  ex := .mkSigma “y param p₁ y₁. !qqAllDef y y₁” (by simp)
  allChanges := .mkSigma “param' param. param' = 0” (by simp)
  exChanges := .mkSigma “param' param. param' = 0” (by simp)

end Negation
end «lp_section_1»
end Arith
end LO
end «lp_nc_section_1»
end
