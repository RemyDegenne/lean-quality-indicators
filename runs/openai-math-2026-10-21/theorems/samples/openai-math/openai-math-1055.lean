namespace OAI

namespace CommonBasesFPRAS

infixr:80 " >>> " => compose

syntax "control" : tactic

macro_rules
| `(tactic| control) => `(tactic|
  first
  | assumption
  | apply controlled_compose <;> control
  | apply controlled_both <;> control
  | apply controlled_branch <;> control
  | exact controlled_atomic _ trivial)

syntax "cc" : tactic

macro_rules
| `(tactic| cc) => `(tactic|
  first
  | assumption
  | exact controlled_wordRange
  | exact controlled_boolNot
  | exact controlled_boolAnd
  | exact controlled_boolOr
  | exact controlled_natEqual
  | exact controlled_natEqZero
  | exact controlled_natSub
  | exact controlled_natDiv
  | exact controlled_natMod
  | exact controlled_natDivRem
  | exact controlled_swap
  | exact controlled_listLength
  | exact controlled_wordLength
  | exact controlled_fromList
  | exact controlled_listReverse
  | exact controlled_listAppend
  | exact controlled_productCode
  | exact controlled_wordGet
  | exact controlled_wordNot
  | exact controlled_wordCount
  | exact controlled_deficiency
  | exact controlled_listAll
  | exact controlled_splitAt
  | exact controlled_take
  | exact controlled_drop
  | exact controlled_headD
  | exact controlled_getD
  | exact controlled_normalizeRat
  | exact controlled_ratAdd
  | exact controlled_ratMul
  | exact controlled_ratDiv
  | exact controlled_ratLess
  | exact controlled_ratMinOne
  | exact controlled_ratSum
  | exact controlled_ratProduct
  | apply controlled_mapWith <;> cc
  | apply controlled_filterWith <;> cc
  | apply controlled_onLeft <;> cc
  | apply controlled_onRight <;> cc
  | apply controlled_letIn <;> cc
  | apply controlled_applyIf <;> cc
  | apply controlled_compose <;> cc
  | apply controlled_both <;> cc
  | apply controlled_branch <;> cc
  | exact controlled_atomic _ trivial)

syntax "ec" : tactic

macro_rules
| `(tactic| ec) => `(tactic|
  first
  | assumption
  | exact Effect.controlled_draw
  | apply Effect.controlled_precompose <;> ec
  | apply Effect.controlled_map <;> ec
  | apply Effect.controlled_bind <;> ec
  | apply Effect.controlled_letIn <;> ec
  | apply Effect.controlled_pure <;> cc
  | apply Effect.controlled_keep <;> ec
  | apply Effect.controlled_choose <;> ec
  | apply Effect.controlled_withContext <;> ec
  | apply Effect.controlled_retainOption <;> ec
  | apply controlled_optionMap <;> cc
  | apply controlled_mapEach <;> cc
  | cc)

namespace MachineCode

open Expression

open scoped Classical

open Expression

open Expression

open scoped Classical

namespace Effect

lemma safe_iterateTrace : OracleSafe (iterateCode (withOptionContext traceAtCode))
    (bankScope iterateTraceScope) := by
  unfold iterateCode
  apply oracleSafe_precompose _ _ iterateTraceScope traceRepeatScope
    (oracleSafe_controlled _ (by cc) _ _ iterateTraceScope_width) safe_repeatTrace
  intro n O S z hz y hy
  have he : (z.1,(true,z.2))=y := Option.some.inj hy
  subst y
  obtain ⟨m,hm,h,hh,j,hj,x,he⟩ := hz.2
  exact ⟨hz.1,m,hm,h,hh,j,hj,x,by rw [he]; rfl⟩

end Effect
end MachineCode
end CommonBasesFPRAS
end OAI
