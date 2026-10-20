public noncomputable section

open ValuativeRel IntermediateField

namespace TauCeti

variable (K : Type*) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable [PerfectField K]

/-- The finite quotient by `P_K U` is the Galois group of the associated tame layer. -/
def quotientTameLayerEquiv (U : OpenNormalSubgroup (Field.absoluteGaloisGroup K)) :
    Field.absoluteGaloisGroup K ⧸ (tameLayerSubgroup K U).toSubgroup ≃ₜ*
      Gal(tameLayer K U/K) :=
  -- Specify both carriers: the fixing subgroup uses the automorphism group instances,
  -- while the source quotient uses the derived absolute Galois group instances.
  ((show Field.absoluteGaloisGroup K ≃ₜ* Gal(AlgebraicClosure K/K) from
      ContinuousMulEquiv.refl _).quotientCongr
    (tameLayerSubgroup K U).toSubgroup (tameLayer K U).fixingSubgroup
    (by
      change (tameLayerSubgroup K U).toSubgroup.map (MonoidHom.id _) = _
      rw [Subgroup.map_id]
      exact (fixingSubgroup_tameLayer K U).symm)).trans
      (absoluteGaloisGroupQuotientEquiv K (tameLayer K U))

end TauCeti
end
