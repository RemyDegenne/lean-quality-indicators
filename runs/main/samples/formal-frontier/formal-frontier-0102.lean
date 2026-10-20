public section

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

variable {J : Type v} {X : J → Scheme.{u}} {Y : Scheme.{u}}

namespace RationalPointSet

theorem schematicallyDense_iff_iInf_eval_ker
    {K : Type u} [Field K] {Y : Over (Spec (.of K))}
    (S : Set (RationalPoint Y)) [IsAffine Y.left] :
    SchematicallyDense S ↔ (⨅ s : S, RingHom.ker (eval s.1)) = ⊥ := by
  rw [schematicallyDense_iff_iInf_appTop_ker]
  simp_rw [eval_ker]

end RationalPointSet
end AlgebraicGeometry
end
end
