@[expose] public section

open Function

namespace Equiv

open Set

variable {ι ι' : Type*} {α : ι → Type*}

theorem piCongrLeft_symm_preimage_univ_pi (f : ι' ≃ ι) (t : ∀ i, Set (α i)) :
    (f.piCongrLeft α).symm ⁻¹' univ.pi (fun i' => t <| f i') = univ.pi t := by
  simpa [f.surjective.range_eq] using piCongrLeft_symm_preimage_pi f univ t

end Equiv
end
