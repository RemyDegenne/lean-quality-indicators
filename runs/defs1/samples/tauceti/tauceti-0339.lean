public section

namespace TauCeti

open CategoryTheory ContRepresentation TopRep _root_.ContinuousCohomology

universe u v w

namespace TopPairing

variable {R : Type u} [CommRing R] [TopologicalSpace R]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : TopRep.{max v w} R G} (P : TopPairing X Y Z)

/-- **The cup product on continuous cohomology**, `Hᵐ(G, X) →ₗ[R] Hⁿ(G, Y) →ₗ[R] Hᵐ⁺ⁿ(G, Z)`, for
a coefficient pairing `P : TopPairing X Y Z`: the class of `a ⌣ b` on the classes of the cocycles
`a` and `b` (`cup_π`). -/
noncomputable def cup (m n : ℕ) :
    continuousCohomology m X →ₗ[R] continuousCohomology n Y →ₗ[R] continuousCohomology (m + n) Z :=
  (homogeneousCochains X).descHomologyₗ
    ((homogeneousCochains Y).descHomologyₗ
      ((P.cupCocycles m n).compr₂ (π Z (m + n)).hom.toLinearMap).flip
      (fun b hb ↦ LinearMap.ext fun a ↦
        P.homologyπ_cupCocycles_eq_zero_of_right_eq_zero m n a b hb)).flip
    (fun a ha ↦ LinearMap.ext fun β ↦ by
      obtain ⟨b, rfl⟩ := (homogeneousCochains Y).homologyπ_surjective n β
      rw [LinearMap.flip_apply, HomologicalComplex.descHomologyₗ_π, LinearMap.flip_apply,
        LinearMap.compr₂_apply, LinearMap.zero_apply]
      exact P.homologyπ_cupCocycles_eq_zero_of_left_eq_zero m n a ha b)

end TopPairing
end TauCeti
end
