public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

noncomputable section

namespace EffectiveDivisorOfDegree

/-- Change the degree index of a fixed-degree effective divisor along an equality. -/
protected def cast {d e : ℕ} (h : d = e) :
    EffectiveDivisorOfDegree X d ≃ EffectiveDivisorOfDegree X e where
  toFun D := ⟨D, D.property.1, D.property.2.trans (by exact_mod_cast h)⟩
  invFun D := ⟨D, D.property.1, D.property.2.trans (by exact_mod_cast h.symm)⟩

end EffectiveDivisorOfDegree
end
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
