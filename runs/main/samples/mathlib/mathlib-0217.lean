@[expose] public section

open Set Function

variable {α β γ δ : Type*} {ι : Sort*} {s t u : Set α}

scoped[MeasureTheory] notation "MeasurableSet[" m "]" => @MeasurableSet _ m

open scoped MeasureTheory

export MeasurableSingletonClass (measurableSet_singleton)

namespace MeasurableSpace

section CompleteLattice

lemma iSup_generateFrom (s : ι → Set (Set α)) :
    ⨆ i, generateFrom (s i) = generateFrom (⋃ i, s i) :=
  (@MeasurableSpace.giGenerateFrom α).gc.l_iSup.symm

end CompleteLattice
end MeasurableSpace
end
