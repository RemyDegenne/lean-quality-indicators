namespace P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq

set_option autoImplicit false

set_option maxHeartbeats 3200000

noncomputable section

namespace DS575Sol

open CongruenceSubgroup ModularForm SlashInvariantForm Matrix MatrixGroups Function OnePoint Matrix.SpecialLinearGroup Matrix.GeneralLinearGroup

open UpperHalfPlane hiding I

open scoped ModularForm

local notation "𝒢(" M ")" =>
  ((CongruenceSubgroup.Gamma M : Subgroup SL(2, ℤ)) : Subgroup (GL (Fin 2) ℝ))

section Average

variable (N M : ℕ) [NeZero N] {k : ℤ}

scoped instance instNormalGamma (n : ℕ) : (CongruenceSubgroup.Gamma n).Normal := Gamma_normal n

scoped instance instFintypeQ : Fintype (Q N M) := Fintype.ofFinite _

lemma Fbar_add (v w : CuspForm 𝒢(N) k) (q : Q N M) :
    Fbar N M (v + w) q = Fbar N M v q + Fbar N M w q := by
  induction q using QuotientGroup.induction_on with
  | H a => rw [Fbar_mk, Fbar_mk, Fbar_mk, slashV_add]

end Average
end DS575Sol
end
end P2MW.S_CuspForm_exists_sum_eq_forall_gamma1_div_slash_eq
