public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X : Type*}

namespace EffectiveDivisorOfDegree

variable {d e : ℕ}

noncomputable section

lemma sup_le {F : WeilDivisor X} {D : EffectiveDivisorOfDegree X d}
    {E : EffectiveDivisorOfDegree X e} (hDF : (D : WeilDivisor X) ≤ F)
    (hEF : (E : WeilDivisor X) ≤ F) : (sup D E : WeilDivisor X) ≤ F := by
  rw [coe_sup]
  exact _root_.sup_le hDF hEF

end
end EffectiveDivisorOfDegree
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
