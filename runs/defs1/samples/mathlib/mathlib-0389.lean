@[expose] public section

namespace CategoryTheory

open Limits

variable (C : Type*) [Category* C]

/--
The extensive coverage on an extensive category `C`

TODO: use general colimit API instead of `IsIso (Sigma.desc π)`
-/
def extensiveCoverage [FinitaryPreExtensive C] : Coverage C where
  coverings B := { S | ∃ (α : Type) (_ : Finite α) (X : α → C) (π : (a : α) → (X a ⟶ B)),
    S = Presieve.ofArrows X π ∧ IsIso (Sigma.desc π) }
  pullback := by
    intro X Y f S ⟨α, hα, Z, π, hS, h_iso⟩
    let Z' : α → C := fun a ↦ pullback f (π a)
    let π' : (a : α) → Z' a ⟶ Y := fun a ↦ pullback.fst _ _
    refine ⟨@Presieve.ofArrows C _ _ α Z' π', ⟨?_, ?_⟩⟩
    · constructor
      exact ⟨hα, Z', π', ⟨by simp only,
        FinitaryPreExtensive.isIso_sigmaDesc_fst (fun x => π x) f h_iso⟩⟩
    · intro W g hg
      rcases hg with ⟨a⟩
      refine ⟨Z a, pullback.snd _ _, π a, ?_, by rw [CategoryTheory.Limits.pullback.condition]⟩
      rw [hS]
      exact Presieve.ofArrows.mk a

end CategoryTheory
end
