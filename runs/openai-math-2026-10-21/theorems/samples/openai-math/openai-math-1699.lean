namespace OAI

section

open MeasureTheory ProbabilityTheory

open scoped ENNReal Classical

namespace DirectionalTransience

namespace EpisodeChart

variable {d k : ℕ} {e f : Direction d} {r : ℝ → ℝ}

lemma measurable_nextProfile (c : EpisodeChart (k:=k) e f r) (hef : e.1 ≠ f.1)
    (fexp g b : ℝ) (j : ℕ) (grow : Bool) :
    @Measurable _ _ (rowSigma (BelowHeight (realPosition (step e)) ((c.height+j:ℕ):ℝ))) _
      (c.nextProfile hef fexp g b j grow) := by
  apply Measurable.subtype_mk
  have hm := measurable_subtype_coe.comp
    (seedSeparatedProfile_measurable e f hef c.height (r (c.nextScale fexp g b grow)) j
      c.layerProfile c.measurable_layerProfile)
  convert hm using 1 <;> first | rfl | rw [Nat.cast_add]

end EpisodeChart
end DirectionalTransience
end
end OAI
