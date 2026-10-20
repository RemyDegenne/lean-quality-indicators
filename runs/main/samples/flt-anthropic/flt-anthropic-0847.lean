namespace P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace CarayolMatrix

open IsLocalRing Matrix

namespace Datum

variable {T : Type} [CommRing T] [IsLocalRing T]

variable {ι : Type} {A : ι → Type} [∀ i, CommRing (A i)] [∀ i, IsLocalRing (A i)]
  [∀ i, Algebra T (A i)] [∀ i, IsLocalHom (algebraMap T (A i))]

variable {m : Type} [Fintype m] [DecidableEq m]

variable {G : Type*} [Monoid G] {κ : Type} [Fintype κ] [DecidableEq κ]

set_option quotPrecheck false in
local notation "k" => ResidueField T

set_option quotPrecheck false in
local notation "𝔸" => (∀ i, A i)

set_option quotPrecheck false in
local notation "φ" => algebraMap T (∀ i, A i)

variable (D : Datum T A m G κ)

theorem Ψ_mulT (s t : κ → T) : D.Ψ (D.mulT s t) = D.Ψ s * D.Ψ t := by
  rw [mulT, map_sum]
  simp_rw [map_sum, LinearMap.map_smul, ← R_eq_Ψ_d, map_mul]
  rw [Ψ_apply, Ψ_apply, Finset.sum_mul]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [smul_mul_assoc, mul_smul_comm, smul_smul, ← map_mul (algebraMap T (∀ i, A i)),
    algebraMap_smul]

end Datum
end CarayolMatrix
end
end P2MW.S_GaloisRepAdic_exists_baseChangeAlong_isEquiv_of_forall_trace_eq
