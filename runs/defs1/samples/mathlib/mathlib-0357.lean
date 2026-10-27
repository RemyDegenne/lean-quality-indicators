@[expose] public section

variable (R K L M : Type*) [CommRing R] [LieRing L] [LieAlgebra R L]
  [AddCommGroup M] [Module R M] [LieRingModule L M] [LieModule R L M]

local notation "φ" => LieModule.toEnd R L M

open LinearMap (trace)

open Set Module

section LieAlgebra

/-- A finite, free (as an `R`-module) Lie algebra `L` carries a bilinear form on `L`.

This is a specialisation of `LieModule.traceForm` to the adjoint representation of `L`. -/
noncomputable abbrev killingForm : LinearMap.BilinForm R L := LieModule.traceForm R L L

end LieAlgebra
end
