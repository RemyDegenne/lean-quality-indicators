import Mathlib
import Definitions.Def_CuspForm_Gamma1HeckeOperators
import P2M.Util
namespace P2MW.S_CuspForm_heckeTLinOne_slashOfMemGamma0

set_option autoImplicit false

open CongruenceSubgroup
open scoped MatrixGroups ModularForm

theorem solution
    {M : ℕ} (k : ℤ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓM : ¬ ℓ ∣ M)
    {γ : SL(2, ℤ)} (hγ : γ ∈ Gamma0 M) (f : CuspForm (Gamma1 M) k) :
    CuspForm.heckeTLinOne k hℓ hℓM (CuspForm.slashOfMemGamma0 M k hγ f) =
      CuspForm.slashOfMemGamma0 M k hγ (CuspForm.heckeTLinOne k hℓ hℓM f) := by
  obtain ⟨σ, hσ⟩ := CuspForm.exists_isDiamondLift_of_coprime (M := M)
    ((Nat.Prime.coprime_iff_not_dvd hℓ).2 hℓM)
  refine DFunLike.ext' ?_
  rw [CuspForm.coe_heckeTLinOne_apply_of_isDiamondLift k hℓ hℓM hσ, CuspForm.coe_slashOfMemGamma0,
    CuspForm.coe_slashOfMemGamma0, CuspForm.coe_heckeTLinOne_apply_of_isDiamondLift k hℓ hℓM hσ]
  exact (CuspForm.Gamma1Hecke.heckeU_add_slash_heckeDiagMatrix_slash_of_mem_Gamma0 k hℓ hℓM
    (fun g hg => SlashInvariantFormClass.slash_action_eq f g hg) σ hσ.1 hσ.2 hγ).symm
