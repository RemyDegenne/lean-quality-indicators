set_option warningAsError true

@[expose] public section

noncomputable section

universe uG uA uB uC uN uE uQ uE'

namespace PointwiseContinuousMulAction

variable {G : Type uG} {A : Type uA}
  [Group G] [CommGroup A] [TopologicalSpace A] [IsTopologicalGroup A]

/-- The set of action differences `g • a * a⁻¹`. -/
def differenceSet (ρ : PointwiseContinuousMulAction G A) : Set A :=
  {x | ∃ (g : G) (a : A), x = ρ g a * a⁻¹}

end PointwiseContinuousMulAction
end
end
