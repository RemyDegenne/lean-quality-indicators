public section

universe u v w

open CategoryTheory TensorProduct

namespace Module.Grassmannian

variable {R : Type u} [CommRing R] {M : Type v} [AddCommGroup M] [Module R M] {k : ℕ}

open ChartAlgebra

section Triple

variable (R)

variable {A : Type w} [CommRing A] [Algebra R A]

/-- `R`-algebra maps `TripleAlgebra R x y z → A` are the points of `G(k, A ⊗[R] M; A)` lying in the
charts at `x`, `y` and `z`: the point attached to `g` is the point of the overlap of the charts at
`x` and `y` classified by the restriction of `g` to `OverlapAlgebra R x y`. -/
noncomputable def tripleHomEquiv (x y z : Fin k → M) (A : Type w) [CommRing A] [Algebra R A] :
    (TripleAlgebra R x y z →ₐ[R] A) ≃
      ↥(chart A (fun i ↦ (1 : A) ⊗ₜ[R] x i) ∩ chart A (fun i ↦ (1 : A) ⊗ₜ[R] y i) ∩
        chart A (fun i ↦ (1 : A) ⊗ₜ[R] z i)) where
  toFun g := ⟨(overlapHomEquiv R x y A (g.comp (IsScalarTower.toAlgHom R _ _))).1,
    (overlapHomEquiv R x y A _).2, by
      rw [coe_overlapHomEquiv_apply, chartHomEquiv_mem_chart_iff]
      exact (IsLocalization.Away.algebraMap_isUnit (S := TripleAlgebra R x y z)
        (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y) (transitionDet R x z))).map g⟩
  invFun N := tripleLift R x y z N
  left_inv g := IsLocalization.algHom_ext (Submonoid.powers
      (algebraMap (ChartAlgebra R x) (OverlapAlgebra R x y) (transitionDet R x z))) <|
    (tripleLift_comp R x y z _).trans <| (overlapHomEquiv R x y A).symm_apply_apply _
  right_inv N := Subtype.ext <| by
    simp only [tripleLift_comp, Equiv.apply_symm_apply]

end Triple
end Module.Grassmannian
end
