public section

namespace TauCeti.ContCohomology

universe uG uM uN uP

section CupZeroOne

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

include hμ hequiv

variable [ContinuousSMul G N] [ContinuousSMul G P]

/-- **The `(0,1)` cup product**, `(m ⌣ b) g = μ m (b g)`. For invariant `m` this is the
coefficient map induced by `μ m`. -/
noncomputable def explicitCup01 : H0 G M →+ H1 G N →+ H1 G P :=
  AddMonoidHom.mk'
    (fun m => explicitCoeff1 G N (pairingLeft μ hequiv m) (continuous_pairingLeft μ hequiv hμ m))
    fun m m' => AddMonoidHom.ext fun x => by
      induction x using QuotientAddGroup.induction_on with
      | _ c =>
        rw [AddMonoidHom.add_apply, explicitCoeff1_mk, explicitCoeff1_mk, explicitCoeff1_mk,
          ← QuotientAddGroup.mk_add]
        exact congrArg (fun z : Z1 G P => (z : H1 G P))
          (Subtype.ext (funext fun g => by simp [cocyclesMap1_coe]))

end CupZeroOne
end TauCeti.ContCohomology
end
