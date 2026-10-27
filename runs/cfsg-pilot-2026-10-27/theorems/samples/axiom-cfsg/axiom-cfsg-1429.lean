public section

namespace CFSG.GH74.GLS.C3.Layer1.PumpRigid

open Subgroup CFSG CFSG.ABGLocalTools CFSG.GH74.GLS CFSG.GH74.GLS.TwoThin
  CFSG.ComponentClassification CFSG.LocalAnalysis.ComponentInitial
  CFSG.GH74.GLS.C3.Layer1.PumpCalc

open scoped commutatorElement

section Main

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable {x y t : G} {K Q K' Λ : Subgroup G} {hxY : x ∈ centralizer ({t} : Set G)}

theorem hcov (S : Setup x y K Q t K' Λ hxY) : ∀ r ∈ Q ⊓ centralizer ({t} : Set G),
    r ∈ Q ⊓ CxK t K' ∨ x * r ∈ Q ⊓ CxK t K' := by
  intro r hr
  rcases S.h.step1 hr.2 (S.Q_le_C hr.1) with h1 | h1
  · exact Or.inl ⟨hr.1, h1⟩
  · exact Or.inr ⟨mul_mem S.hxQ hr.1, h1⟩

end Setup
end Main
end CFSG.GH74.GLS.C3.Layer1.PumpRigid
end
