public section

namespace TauCeti

namespace AlgebraicGeometry

namespace WeilDivisor

namespace EffectiveDivisorOfDegree

variable {X : Type*} {d e : ℕ}

noncomputable section

/-- The residual fixed-degree effective divisor `D - E`, defined when `E ≤ D`.

If `D` has degree `e` and `E` has degree `d`, the residual has degree `e - d`. -/
@[expose]
def subOfLe (D : EffectiveDivisorOfDegree X e) (E : EffectiveDivisorOfDegree X d)
    (hED : (E : WeilDivisor X) ≤ D) : EffectiveDivisorOfDegree X (e - d) :=
  ⟨(D : WeilDivisor X) - E, le_iff_isEffective_sub.mp hED, by
    have hde : d ≤ e := EffectiveDivisorOfDegree.degree_le_of_le hED
    rw [degree_sub, D.degree_eq, E.degree_eq]
    exact (Int.ofNat_sub hde).symm⟩

end
end EffectiveDivisorOfDegree
end WeilDivisor
end AlgebraicGeometry
end TauCeti
end
