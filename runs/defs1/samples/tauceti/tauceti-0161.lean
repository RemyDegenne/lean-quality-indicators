public section

noncomputable section

namespace TauCeti

open ContCohomology

universe u v

variable {K : Type u} [Field K] {L : Type v} [Field L] [Algebra K L]

section FiniteGalois

variable [Normal K L]
  (sigma : L →ₐ[K] SeparableClosure K) (n : ℕ)

/-- The roots-of-unity representation of `Gal(L/K)`, obtained by factoring the absolute Galois
action through the subgroup fixing `sigma(L)`. -/
def kummerCoeffFiniteRepresentation
    (hN : ∀ g : AbsoluteGaloisGroup K, g ∈ sigma.fieldRange.fixingSubgroup →
      ∀ xi : KummerCoeff K n, g • xi = xi) :
    Representation (ZMod n) Gal(L/K) (KummerCoeff K n) := by
  let rho : Representation (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n) :=
    Representation.ofDistribMulAction (ZMod n) (AbsoluteGaloisGroup K) (KummerCoeff K n)
  let _ : Representation.IsTrivial
      (rho.comp sigma.fieldRange.fixingSubgroup.subtype) :=
    ⟨fun g ↦ by
      apply LinearMap.ext
      intro xi
      exact hN g g.2 xi⟩
  exact (rho.ofQuotient sigma.fieldRange.fixingSubgroup).comp
    (quotientFixingSubgroupFieldRangeEquiv K L sigma).symm.toMonoidHom

end FiniteGalois
end TauCeti
end
end
