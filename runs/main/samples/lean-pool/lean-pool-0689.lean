@[expose] public section

namespace Stafford38.WeylSymbolCompatibility

open Stafford

open AlgebraicAnalysis

open Stafford38.Characteristic

open Stafford38.CharacteristicLinearAction

open Stafford38.WeylFiltration

open Stafford38.WeylIteratedEquivalence

open Stafford38.WeylLeadingSymbol

open Stafford38.WeylPBW

open Stafford38.WeylSymplectic

noncomputable section

universe u

variable (k : Type u) [Field k]

theorem algHom_orderedMonomial_principal_zero
    {r : ℕ} (f : PresentedWeyl k 0 →ₐ[k] PresentedWeyl k r)
    (g : PhaseVar 0 → SymbolRing k r)
    (a p : Fin 0 → ℕ) :
    presentedPrincipalComponent k (@bernsteinWeight r)
        (monomialWeight (@bernsteinWeight 0) (phaseExponent a p))
        (f (presentedOrderedMonomial k 0 a p)) =
      MvPolynomial.aeval g
        (MvPolynomial.monomial (phaseExponent a p) (1 : k)) := by
  have hphase : phaseExponent a p = 0 := by
    ext i
    cases i with
    | inl i => exact Fin.elim0 i
    | inr i => exact Fin.elim0 i
  rw [hphase]
  simp [presentedOrderedMonomial, principal_one_bernstein, monomialWeight]

end
end Stafford38.WeylSymbolCompatibility
end
