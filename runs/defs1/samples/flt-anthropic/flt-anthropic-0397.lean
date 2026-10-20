namespace P2MW.S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq

set_option autoImplicit false

set_option linter.unusedVariables false

set_option linter.unusedSectionVars false

open scoped MatrixGroups

open CerednikDrinfeld CerednikDrinfeld.Omega CerednikDrinfeld.Mumford CerednikDrinfeld.BruhatTits LT.LatticeTree MulAction

noncomputable section

namespace HarmV0

section Frame

variable {R K₀ : Type} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [Field K₀] [Algebra R K₀]
  [IsFractionRing R K₀]

variable {K : Type} [Field K] [Algebra K₀ K]

variable {Γ₀ : Type} [LinearOrderedCommGroupWithZero Γ₀] [Valued K Γ₀]

variable [DecidableEq K₀]

variable (R K₀) in

def repFinset (ϖ : R) [Fintype (R ⧸ Ideal.span {ϖ})] : Finset K₀ :=
  Finset.univ.image fun x : R ⧸ Ideal.span {ϖ} => algebraMap R K₀ (Quotient.out x)

end Frame
end HarmV0
end
end P2MW.S_CerednikDrinfeld_Omega_exists_int_neighbours_sum_eq_zero_v_apply_smul_eq
