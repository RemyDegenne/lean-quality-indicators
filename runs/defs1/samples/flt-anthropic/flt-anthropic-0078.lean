set_option autoImplicit false

noncomputable section

namespace GaloisRep

local notation "ℚ̄" => AlgebraicClosure ℚ

local notation "Gal" => (AlgebraicClosure ℚ ≃ₐ[ℚ] AlgebraicClosure ℚ)

namespace InertiaRing

variable (A : ValuationSubring ℚ̄)

variable {A} in

def mkO (x : ℚ̄) (hxA : x ∈ A) (hfix : ∀ σ : Gal, σ ∈ A.inertiaSubgroupIn ℚ → σ x = x) : inertiaRing A :=
  ⟨x, GaloisRep.mem_inertiaRing_iff.mpr ⟨hxA, GaloisRep.mem_inertiaField_iff.mpr hfix⟩⟩

end InertiaRing
end GaloisRep
end
