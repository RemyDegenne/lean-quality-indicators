namespace OAI

section

namespace Thomason.Construction.NonsingularLastVertex

open CategoryTheory CategoryTheory.Limits Opposite

open scoped Simplicial

noncomputable section

variable {X : SSet.{0}} [X.Nonsingular]

theorem restrictedMap_weak_of_empty (S : Set X.N) [IsEmpty S] :
    realizationWeakEquivalences (restrictedMap S) := by
  have hs : IsInitial (nerve S) := SSet.isInitialOfNotNonempty (by
    rintro ⟨s⟩
    exact isEmptyElim (s.obj 0))
  have he : faceUnion S = ⊥ := by
    apply le_bot_iff.mp
    apply iSup_le
    intro s
    exact isEmptyElim s
  have ht : IsInitial (faceUnion S).toSSet := by
    rw [he]
    exact SSet.Subcomplex.isInitialBot
  have hf : restrictedMap S = (hs.uniqueUpToIso ht).hom := hs.hom_ext _ _
  rw [hf]
  exact realizationWeakEquivalences.of_isIso _

end
end Thomason.Construction.NonsingularLastVertex
end
end OAI
