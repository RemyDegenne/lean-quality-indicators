@[expose] public section

open Function Set

universe u v

namespace ProfiniteGrp

/-- The kernel of a continuous multiplicative homomorphism out of the
primewise p-adic group, regarded as an ideal of its underlying product ring.

Uses Mathlib’s kernel, closed-subgroup and p-adic product APIs; this general ideal
construction is not attributed to a printed procyclic theorem. -/
noncomputable def primewisePadicKernelIdeal
    {Y : Type v} [Group Y] [TopologicalSpace Y] [T1Space Y]
    (f : primewisePadic.{u} →ₜ* Y) : Ideal primewisePadicRing.{u} := by
  let φ : Multiplicative primewisePadicRing.{u} →ₜ* Y :=
    f.comp (primewisePadicRingMultiplicativeEquiv :
      Multiplicative primewisePadicRing.{u} →ₜ* primewisePadic.{u})
  let K : AddSubgroup primewisePadicRing.{u} :=
    φ.toMonoidHom.ker.toAddSubgroup'
  apply K.toIdealOfIsClosedOfDenseIntCast
  · change IsClosed ((fun x : primewisePadicRing.{u} ↦
        φ (Multiplicative.ofAdd x)) ⁻¹' {1})
    exact isClosed_singleton.preimage
      (φ.continuous_toFun.comp continuous_ofAdd)
  · exact denseRange_intCast_primewisePadicRing

end ProfiniteGrp
end
