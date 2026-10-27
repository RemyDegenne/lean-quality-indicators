public section

namespace CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine

open Subgroup

theorem jankoFrameExists : JankoFrameExists := by
  intro G _ _ z hz hH
  obtain ⟨e⟩ := hH.nonempty_mulEquiv
  exact ⟨Janko.frame hz hH e⟩

end CFSG.ProperTwoGeneratedCore.Lemma37.TwoANine
end
