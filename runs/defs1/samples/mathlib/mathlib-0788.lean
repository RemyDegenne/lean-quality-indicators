@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/--
The sheaf of continuous maps `U ↦ C(U, ℤ_[ℓ])` on the pro-étale site. This the coefficient
sheaf for `ℓ`-adic cohomology.
[Definition 6.8.1.][proetale2015]
-/
noncomputable def ellAdicSheaf (ℓ : ℕ) [Fact ℓ.Prime] :
    Sheaf (ProEt.topology X) Ab.{u} :=
  ((ProEt.forget X ⋙ Over.forget _).sheafPushforwardContinuous _ _ proetaleTopology).obj
    ⟨continuousMapPresheafAb (ℤ_[ℓ]), .of_le proetaleTopology_le_fpqcTopology <|
      isSheaf_fpqcTopology_continuousMapPresheafAb _⟩

end AlgebraicGeometry.Scheme
end
