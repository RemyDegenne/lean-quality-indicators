set_option autoImplicit false

open NumberField IsDedekindDomain CategoryTheory

noncomputable section

namespace M4aHerbrand

section Carrier

variable {R F : Type*} [CommRing R] [IsDedekindDomain R] [Field F] [Algebra R F] [IsFractionRing R F]

variable (R F)

def idelesTrivialOn (T : Set (HeightOneSpectrum R)) : Subgroup (AdeleRing R F)ˣ where
  carrier := {x | infPart x = 1 ∧ ∀ w ∈ T, finPart w x = 1}
  one_mem' := ⟨map_one _, fun w _ => map_one _⟩
  mul_mem' {x y} hx hy := ⟨by rw [map_mul, hx.1, hy.1, one_mul], fun w hw => by rw [map_mul, hx.2 w hw, hy.2 w hw, one_mul]⟩
  inv_mem' {x} hx := ⟨by rw [map_inv, hx.1, inv_one], fun w hw => by rw [map_inv, hx.2 w hw, inv_one]⟩

end Carrier
end M4aHerbrand
end
