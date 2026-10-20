@[expose] public section

universe u

namespace Ideal

variable {R : Type u} [Ring R]

/-- Lift an ideal coordinate to an original-ring principal unit using the
Jacobson-radical condition. Its ring value is `1 + x`. -/
noncomputable def principalUnitsMk (I : Ideal R) (hI : I ≤ Ring.jacobson R)
    (x : I) : MulAction.stabilizer Rˣ (Submodule.Quotient.mk (1 : R) : R ⧸ I) :=
  ⟨(show IsUnit (1 + (x : R)) from by
    exact isUnit_one_add_of_mem_ringJacobson (x : R) (hI x.property)).unit, by
    rw [mem_stabilizer_quotient_one, IsUnit.unit_spec]
    simpa only [add_sub_cancel_left] using x.property⟩

end Ideal
end
