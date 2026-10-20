public section

namespace TauCeti.ContCohomology

universe u v w x

section DegreeOne

section ExplicitCup01

variable (G : Type u) [Group G] [TopologicalSpace G] [SeparatelyContinuousMul G]
  (M : Type v) [AddCommGroup M] [TopologicalSpace M] [DistribMulAction G M]
  (N : Type w) [AddCommGroup N] [TopologicalSpace N] [IsTopologicalAddGroup N]
    [DistribMulAction G N] [ContinuousSMul G N]
  (P : Type x) [AddCommGroup P] [TopologicalSpace P] [IsTopologicalAddGroup P]
    [DistribMulAction G P] [ContinuousSMul G P]
  (U : Subgroup G) [U.FiniteIndex] (hU : IsOpen (U : Set G))
  (μ : M →+ N →+ P) (hμ : Continuous fun p : M × N => μ p.1 p.2)
  (hequiv : ∀ (g : G) (m : M) (y : N), μ (g • m) (g • y) = g • μ m y)

include hU hμ hequiv

theorem explicitCup_projection (a : H0 G M) (b : H1 U N) :
    explicitCor1 G P U hU
        (explicitCup01 U M N P μ hμ (fun g m y => hequiv (g : G) m y)
          (explicitRes0 G M U a) b) =
      explicitCup01 G M N P μ hμ hequiv a (explicitCor1 G N U hU b) := by
  -- Replace `res⁰ a` by an element whose underlying coefficient is literally `a`, so that the
  -- cup cochains on the two sides are pairings against the same element of `M`.
  have hres : explicitRes0 G M U a = ⟨(a : M), fun g : U => a.2 (g : G)⟩ :=
    Subtype.ext (coe_explicitRes0 G M U a)
  induction b using QuotientAddGroup.induction_on with
  | _ c =>
    rw [hres, explicitCup01_mk, explicitCor1_mk, explicitCor1_mk, explicitCup01_mk]
    refine congrArg (fun z : Z1 G P => (z : H1 G P)) (Subtype.ext ?_)
    simp only [coe_cocyclesCor1]
    funext γ
    exact (map_cochainsCor1 G N U Quotient.out Quotient.out_eq (μ (a : M))
      (fun g y => pairingLeft_smul μ hequiv a g y) (c : U → N) γ).symm

end ExplicitCup01
end DegreeOne
end TauCeti.ContCohomology
end
