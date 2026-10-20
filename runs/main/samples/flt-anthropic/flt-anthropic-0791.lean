namespace P2MW.S_CohCarrier_jDeg_iDeg_four_identities_of_dvd

set_option autoImplicit false

set_option linter.unusedSectionVars false

noncomputable section

namespace FourIdentitiesDvdSol

open CohCarrier CongruenceSubgroup

open scoped MatrixGroups

attribute [local instance] Subgroup.fintypeQuotientOfFiniteIndex

variable {N q : ℕ} [NeZero N] [NeZero q]
  (h1 : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) 1)
  (hq' : LevelLE N (N * q) (⊤ : Subgroup (ZMod N)ˣ) (⊤ : Subgroup (ZMod (N * q))ˣ) q)

variable {A : Type} [AddCommGroup A]

theorem pushChar_one_iDeg_q_eq (φ : H1 N ⊤ A) :
    pushChar N (N * q) ⊤ ⊤ 1 A h1 (iDeg' N (N * q) ⊤ ⊤ q A hq' φ)
      = (φ.comp (conjLowerL N ⊤ q).toAdditive).comp
          (Subgroup.inclusion (range_iotaDeg_one_le (q := q) h1)).toAdditive := by
  refine AddMonoidHom.ext fun a => ?_
  set x : ↥((iotaDeg N (N * q) ⊤ ⊤ 1 h1).range) := Additive.toMul a with hx
  set γ' : ↥(GammaH (N * q) ⊤) :=
    ((iotaDeg N (N * q) ⊤ ⊤ 1 h1).ofInjective (iotaDeg_injective N (N * q) ⊤ ⊤ 1 h1)).symm x with hγ'
  have hιγ' : iotaDeg N (N * q) ⊤ ⊤ 1 h1 γ' = (x : ↥(GammaH N ⊤)) :=
    MonoidHom.apply_ofInjective_symm (iotaDeg_injective N (N * q) ⊤ ⊤ 1 h1) x
  have hcoe : (γ' : SL(2, ℤ)) = ((x : ↥(GammaH N ⊤)) : SL(2, ℤ)) := by
    rw [← coe_iotaDeg_one' h1 γ', hιγ']

  show φ (Additive.ofMul (iotaDeg N (N * q) ⊤ ⊤ q hq' γ')) =
    φ (Additive.ofMul (conjLowerL N ⊤ q ⟨(x : ↥(GammaH N ⊤)), range_iotaDeg_one_le h1 x.2⟩))
  congr 2
  apply Subtype.ext
  have key : ∀ (B C : SL(2, ℤ)) (hB : (q : ℤ) ∣ B 1 0) (hC : (q : ℤ) ∣ C 1 0), B = C →
      conjLowerMat q B hB = conjLowerMat q C hC := by
    rintro B C hB hC rfl; rfl
  exact key _ _ (hq'.dvd_entry γ')
    (dvd_of_mem_GammaHLower N ⊤ q ⟨_, range_iotaDeg_one_le h1 x.2⟩) hcoe

end FourIdentitiesDvdSol
end
end P2MW.S_CohCarrier_jDeg_iDeg_four_identities_of_dvd
