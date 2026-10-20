public section

open MeasureTheory Set Filter

open Filter

open scoped ENNReal

open scoped Convolution

open scoped Topology

open CKN CKN.Foundation.Parabolic CKN.Foundation.Heat

noncomputable section

namespace CKN.Leray

/-- The full velocity--gradient--pressure momentum integrand in product
coordinates, used by `thm:assoc-pressure`. -/
@[expose]
def associatedPressureMomentumProductIntegrand
    (u : Vec3 × ℝ → Vec3) (Du : Vec3 × ℝ → Fin 3 → Vec3)
    (p : Vec3 × ℝ → ℝ) (φ : Vec3 × ℝ → Vec3) (z : Vec3 × ℝ) : ℝ :=
  -(∑ i : Fin 3, u z i * CKN.timePartialProd (fun q => φ q i) z)
    - ∑ i : Fin 3, ∑ j : Fin 3,
        u z i * u z j * CKN.spatialPartialProd (fun q => φ q i) j z
    + ∑ i : Fin 3, ∑ j : Fin 3,
        Du z i j * CKN.spatialPartialProd (fun q => φ q i) j z
        - p z * ∑ i : Fin 3, CKN.spatialPartialProd (fun q => φ q i) i z

end CKN.Leray
end
end
