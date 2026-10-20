set_option warningAsError true

@[expose] public section

noncomputable section

universe uG uA uB uC uN uE uQ uE'

namespace PointwiseContinuousMulAction

variable {G : Type uG} {A : Type uA}
  [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- Algebraic universal property, bundled continuously for the quotient
topology: a continuous homomorphism killing every action difference factors
through the unclosed algebraic coinvariants. -/
def algebraicLift {B : Type uB} [Group B] [TopologicalSpace B]
    (ρ : PointwiseContinuousMulAction G A) (f : A →ₜ* B)
    (hf : ρ.KillsDifferences f) : ρ.AlgebraicCoinvariants →ₜ* B where
  toMonoidHom := QuotientGroup.lift ρ.differenceSubgroup f
    (ρ.differenceSubgroup_le_ker f.toMonoidHom hf)
  continuous_toFun := by
    rw [(QuotientGroup.isQuotientMap_mk ρ.differenceSubgroup).continuous_iff]
    exact f.continuous

end PointwiseContinuousMulAction
end
end
