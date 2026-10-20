@[expose] public section

open Finset

open scoped ENNReal

namespace MeasureTheory

variable {ι : Type*} {α : ι → Type*} {mα : ∀ i, MeasurableSpace (α i)}
  {P : ∀ J : Finset ι, Measure (Π j : J, α j)} {s t : Set (Π i, α i)} {I : Finset ι}
  {S : Set (Π i : I, α i)}

section ProjectiveFamilyContent

lemma projectiveFamilyContent_mono (hP : IsProjectiveMeasureFamily P)
    (hs : s ∈ measurableCylinders α) (ht : t ∈ measurableCylinders α) (hst : s ⊆ t) :
    projectiveFamilyContent hP s ≤ projectiveFamilyContent hP t :=
  addContent_mono isSetSemiring_measurableCylinders hs ht hst

end ProjectiveFamilyContent
end MeasureTheory
end
