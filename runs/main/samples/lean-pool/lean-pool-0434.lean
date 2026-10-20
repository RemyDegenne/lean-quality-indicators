@[expose] public section

noncomputable section «lp_nc_section_1»

namespace LO

namespace Arith

open FirstOrder FirstOrder.Arith

variable {V : Type*} [ORingStruc V] [V ⊧ₘ* 𝐈Sg1]

variable {L : Arith.Language V} {pL : LDef} [Arith.Language.Defined L pL]

scoped prefix:max "^rel " => qqRel

scoped prefix:max "^nrel " => qqNRel

scoped notation "^⊤" => qqVerum

scoped notation "^⊥" => qqFalsum

scoped notation p:69 " ^⋏ " q:70 => qqAnd p q

scoped notation p:68 " ^⋎ " q:69 => qqOr p q

scoped notation "^∀ " p:64 => qqAll p

scoped notation "^∃ " p:64 => qqEx p

namespace Language

namespace UformulaRec1

variable (V)

variable {V}

namespace Construction

variable {β : Blueprint pL} (c : Construction V L β)

variable {param : V}

variable {c}

variable (c β)

variable {β}

variable (param)

lemma graph_unique {p : V} :
    L.IsUFormula p → ∀ {param r r'}, c.Graph param p r → c.Graph param p r' → r = r' := by
  apply Language.IsUFormula.induction_pi1 (P :=
    fun p ↦ ∀ {param r r'}, c.Graph param p r → c.Graph param p r' → r = r')
    (by definability)
  case hrel =>
    intro k R v hkR hv
    simp [c.graph_rel_iff hkR hv]
  case hnrel =>
    intro k R v hkR hv
    simp [c.graph_nrel_iff hkR hv]
  case hverum =>
    simp [c.graph_verum_iff]
  case hfalsum =>
    simp [c.graph_falsum_iff]
  case hand =>
    intro p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr'
    rcases c.graph_and_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_and_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hor =>
    intro p₁ p₂ _ _ ih₁ ih₂ param r r' hr hr'
    rcases c.graph_or_inv hr with ⟨r₁, r₂, h₁, h₂, rfl⟩
    rcases c.graph_or_inv hr' with ⟨r₁', r₂', h₁', h₂', rfl⟩
    rcases ih₁ h₁ h₁'; rcases ih₂ h₂ h₂'; rfl
  case hall =>
    intro p _ ih param r r' hr hr'
    rcases c.graph_all_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_all_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl
  case hex =>
    intro p _ ih param r r' hr hr'
    rcases c.graph_ex_inv hr with ⟨r₁, h₁, rfl⟩
    rcases c.graph_ex_inv hr' with ⟨r₁', h₁', rfl⟩
    rcases ih h₁ h₁'; rfl

end Construction
end UformulaRec1
end Language
end Arith
end LO
end «lp_nc_section_1»
end
