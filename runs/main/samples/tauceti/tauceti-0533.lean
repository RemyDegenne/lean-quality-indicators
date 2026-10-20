public section

namespace TauCeti.ContCohomology

universe uG uM uN uP

section CommOneOne

variable (G : Type uG) [Monoid G] [TopologicalSpace G]
  (M : Type uM) [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M]
  (N : Type uN) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N]
  (P : Type uP) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P]
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (x : N), μ (g • m) (g • x) = g • μ m x)

variable [ContinuousMul G] [ContinuousSMul G M] [ContinuousSMul G N] [ContinuousSMul G P]

include hμ hequiv in
theorem explicitCup11_eq_neg_flip (a : H1 G M) (b : H1 G N) :
    explicitCup11 G M N P μ hμ hequiv a b =
      -explicitCup11 G N M P μ.flip
        (μ.continuous_flip hμ)
        (μ.flip_map_smul hequiv) b a := by
  induction a using QuotientAddGroup.induction_on with
  | _ x =>
    induction b using QuotientAddGroup.induction_on with
    | _ y =>
      rw [explicitCup11_mk, explicitCup11_mk, eq_neg_iff_add_eq_zero, ← QuotientAddGroup.mk_add,
        H2pi_eq_zero_iff]
      exact cup11_add_cup11_flip_mem_B2 G M N P μ hμ hequiv x.2 y.2

end CommOneOne
end TauCeti.ContCohomology
end
