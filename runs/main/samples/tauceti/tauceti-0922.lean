public section

noncomputable section

open scoped MultiplierAlgebra

namespace TauCeti.CStarAction

variable {G A : Type*} [Group G] [TopologicalSpace G] [NonUnitalCStarAlgebra A]

theorem continuous_multiplier_apply_snd (α : CStarAction G A) (m : 𝓜(ℂ, A)) (a : A) :
    Continuous fun g => (α.multiplier g m).snd a := by
  simp only [multiplier_apply_snd]
  exact α.continuous_apply continuous_id (m.snd.continuous.comp (α.continuous_inv_apply a))

end TauCeti.CStarAction
end
end
