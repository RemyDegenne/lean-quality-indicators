public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

variable {X Y : Type*}

noncomputable section

namespace EffectiveDivisorOfDegree

/-- An effective divisor of degree `d` from finitely supported natural multiplicities whose
total multiplicity is `d`. -/
abbrev ofFinsupp (m : X →₀ ℕ) (hm : m.sum (fun _ n => n) = d) :
    EffectiveDivisorOfDegree X d :=
  ⟨WeilDivisor.ofFinsupp m, isEffective_ofFinsupp m, by
    rw [degree_ofFinsupp]
    exact_mod_cast hm⟩

end EffectiveDivisorOfDegree
end
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
