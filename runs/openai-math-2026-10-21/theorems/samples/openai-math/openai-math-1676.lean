namespace OAI

noncomputable section

open scoped Classical BigOperators SchwartzMap

namespace SevenEighths.CenteredMomentSecondLiveBlock

open HeckeFamily CanonicalQuadraticSieve CompletedGauss

open CenteredMomentSecondBlockAggregate CenteredMomentSecondRetainedAggregate

open CenteredMomentSecondPhysicalBlock CenteredMomentSecondSectorRetained

open CenteredMomentSecondCanonical CenteredMomentSecondCanonicalFrequency CenteredMomentSecondCanonicalNonunit

open CenteredMomentCanonicalFirst CenteredMomentSecondRetainedRows CenteredMomentSectorLocalization

open CenteredMomentHeckeColumnWindow CenteredMomentSecondLocalization CenteredMomentActiveSource

local notation "O" => HeckeFamily.O

lemma common_height_zero_of_not_live (η:Character) (t:ℝ)
    (S:Finset (Ideal O)) (β:Ideal O→ℂ) (p:ActiveLabel S β)
    (hp:p∉liveLabels η S β):heightCoeff η t p.val.1*star (heightCoeff η t p.val.2)=0:=by
  rw [mem_liveLabels] at hp
  push Not at hp
  by_cases hc:idealCoeff η p.val.1=0
  · simp only [heightCoeff,hc,zero_mul]
  · simp only [heightCoeff,hp hc,zero_mul,star_zero,mul_zero]

end SevenEighths.CenteredMomentSecondLiveBlock
end
end OAI
