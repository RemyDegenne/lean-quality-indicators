namespace OAI

section

namespace Thomason.Construction

open CategoryTheory

open scoped Simplicial

theorem realization_horn_one_weak (i : Fin 2) :
    realizationWeakEquivalences (Λ[1, i].ι : _ ⟶ (Δ[1] : SSet.{0})) := by
  have hji : i.rev ≠ i := by fin_cases i <;> decide
  have : IsIso (SSet.horn.ι i i.rev hji : (Δ[0] : SSet.{0}) ⟶ Λ[1, i]) :=
    (hornOneIso i i.rev hji).isIso_hom
  apply (realizationWeakEquivalences.cancel_left_of_respectsIso
    (SSet.horn.ι i i.rev hji) _).mp
  rw [SSet.horn.ι_ι]
  exact realization_delta_one_weak i.rev

end Thomason.Construction
end
end OAI
