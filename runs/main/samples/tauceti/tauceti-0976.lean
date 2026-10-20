public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Scheme

variable {X Y : Scheme.{u}} {p : ℕ} [hp : Fact p.Prime]

@[simp]
theorem frobenius_appLE_apply (hX : (p : Γ(X, ⊤)) = 0) (U V : X.Opens)
    (e : V ≤ X.frobenius p hX ⁻¹ᵁ U) (s : Γ(X, U)) :
    (X.frobenius p hX).appLE U V e s =
      X.presheaf.map (homOfLE (e.trans (frobenius_preimage hX U).le)).op s ^ p := by
  rw [Scheme.Hom.appLE, CommRingCat.comp_apply, frobenius_app_apply]
  -- `homOfLE e` and the restriction in the statement are the same map `Γ(X, U) ⟶ Γ(X, V)`,
  -- since `F_X ⁻¹ᵁ U` is `U` by definition
  exact map_pow (X.presheaf.map (homOfLE e).op).hom s p

end AlgebraicGeometry.Scheme
end
