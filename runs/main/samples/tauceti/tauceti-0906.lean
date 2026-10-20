public section

namespace TauCeti.ContCohomology

open Subgroup

open scoped commutatorElement

universe uG uM uA uP

section GradedRestrict

variable {p : ℕ} {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {M : Type uM} [AddCommGroup M] [TopologicalSpace M] [IsTopologicalAddGroup M]
    [DistribMulAction G M]
  {A : Type uA} [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A]
    [DistribMulAction G A]
  {P : Type uP} [AddCommGroup P] [TopologicalSpace P] [T1Space P] [DistribMulAction G P]
  {μ : M →+ A →+ P} {a : Z1 G M} {b : Z1 G A} {h : G → P} (hh : IsHeisenbergCochain μ a b h)
  (htrivP : ∀ (g : G) (x : P), g • x = x)
  (haN : ∀ n : pLowerCentralSeries p G 1, (a : G → M) n = 0)
  (hbN : ∀ n : pLowerCentralSeries p G 1, (b : G → A) n = 0)
  (hP : ∀ x : P, p • x = 0)

namespace IsHeisenbergCochain

variable (htrivM : ∀ (g : G) (m : M), g • m = m) (htrivA : ∀ (g : G) (x : A), g • x = x)

include htrivM htrivA

theorem gradedRestrict_gradedBracket_gradedMkZero (g g' : G) :
    hh.gradedRestrict htrivP haN hbN hP
        (gradedBracket p G 0 0 (gradedMkZero p G g) (gradedMkZero p G g')) =
      μ ((a : G → M) g) ((b : G → A) g') - μ ((a : G → M) g') ((b : G → A) g) := by
  rw [gradedBracket_gradedMkZero, gradedRestrict_gradedMk, coe_mk,
    hh.apply_commutatorElement_of_smul_eq_self htrivM htrivA htrivP]

end IsHeisenbergCochain
end GradedRestrict
end TauCeti.ContCohomology
end
