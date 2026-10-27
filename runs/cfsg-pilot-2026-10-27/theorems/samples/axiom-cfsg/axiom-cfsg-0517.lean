public section

namespace CFSG.CGT.PushingUpLit.SolKNA

open CFSG.CGT.PushingUpLit.SolKAb (MTOutcome STSetting sylowImg)

open CFSG.ComponentClassification.AschbacherTheorem3 (IsQuaternionTwoGroup)

open CFSG.Assembly.LowTwoRank (StatedLieTag StatedClassicalModel)

theorem neg3Table_of_five (h1 : NegModel .PSL 4) (h2 : NegModel .PSL 5) (h3 : NegModel .PSU 4)
    (h4 : NegModel .PSp 2) (h5 : NegModel .trialityD4 0) : Neg3Table := by
  intro X _ _ t n hc hm K hK R
  rcases hc with ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact h1 X hm K hK R
  · exact h2 X hm K hK R
  · exact h3 X hm K hK R
  · exact h4 X hm K hK R
  · exact h5 X hm K hK R

end CFSG.CGT.PushingUpLit.SolKNA
end
