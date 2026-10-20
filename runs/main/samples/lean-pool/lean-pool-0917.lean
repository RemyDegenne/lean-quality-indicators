universe u v

public section

variable {L A : Type*} [Field L] [CommRing A] [Algebra L A]

namespace Subring

variable {π : A →ₐ[L] L} {S : Subring L}

theorem dvd_residueSubring_iff {x y : residueSubring π S} :
    x ∣ y ↔ ∃ z : A, π z ∈ S ∧ (y : A) = x * z := by
  constructor
  · rintro ⟨z, rfl⟩; exact ⟨z, z.2, rfl⟩
  · rintro ⟨z, hz, h⟩; exact ⟨⟨z, hz⟩, Subtype.ext h⟩

end Subring
end
