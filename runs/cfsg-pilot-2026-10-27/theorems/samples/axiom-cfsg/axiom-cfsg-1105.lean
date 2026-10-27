public section

namespace CFSG.Quasithin.A313

open Matrix

variable {Λ : Type} [Group Λ] [Finite Λ]

omit [Finite Λ] in
theorem inf_eq_bot_or_eq {B : Subgroup Λ} {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hM : IsSL2 r ↥(imgOdd B)) (hF : CFSG.fittingSubgroup Λ = CFSG.oddCore Λ) {p : ℕ}
    [Fact p.Prime] (hnat : NaturalSL2Action p Λ (CFSG.fittingSubgroup Λ)) :
    B ⊓ CFSG.oddCore Λ = ⊥ ∨ B ⊓ CFSG.oddCore Λ = CFSG.oddCore Λ := by
  obtain ⟨e, ψ, hψs, hψk, hact⟩ := hnat
  have hKF : B ⊓ CFSG.oddCore Λ ≤ CFSG.fittingSubgroup Λ := fun x hx => hF ▸ hx.2
  have hBK : B ≤ Subgroup.normalizer ((B ⊓ CFSG.oddCore Λ : Subgroup Λ) : Set Λ) := by
    intro b hb
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hb, ?_⟩
    have : Subgroup.normalizer (CFSG.oddCore Λ : Set Λ) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr inferInstance
    rw [this]
    trivial
  have hsolv : ¬ Group.IsSolvable ↥(B.map ψ) := by
    intro hs
    let σ : ↥B →* ↥(B.map ψ) :=
      (ψ.comp B.subtype).codRestrict (B.map ψ) (fun b => ⟨b, b.2, rfl⟩)
    have hσ : Function.Surjective σ := by
      rintro ⟨_, ⟨b, hb, rfl⟩⟩
      exact ⟨⟨b, hb⟩, rfl⟩
    have hkerEq : (rho B).ker = σ.ker := by
      ext b
      rw [mem_ker_rho, MonoidHom.mem_ker]
      constructor
      · intro h
        apply Subtype.ext
        have : (b : Λ) ∈ ψ.ker := by rw [hψk, hF]; exact h
        exact this
      · intro h
        have : (b : Λ) ∈ ψ.ker := congrArg Subtype.val h
        rw [hψk, hF] at this
        exact this
    let e' : ↥(imgOdd B) ≃* ↥(B.map ψ) :=
      (QuotientGroup.quotientKerEquivOfSurjective (rho B) (rho_surjective B)).symm.trans
        ((QuotientGroup.quotientMulEquivOfEq hkerEq).trans
          (QuotientGroup.quotientKerEquivOfSurjective σ hσ))
    have : Group.IsSolvable ↥(imgOdd B) :=
      Group.isSolvable_of_isSolvable_injective (f := e'.toMonoidHom) e'.injective
    exact IsSL2.not_isSolvable hr hr5 hM this
  have := eq_bot_or_eq_of_natural (CFSG.fittingSubgroup Λ) e ψ hact B (B ⊓ CFSG.oddCore Λ) hKF
    hBK hsolv
  rcases this with h | h
  · exact Or.inl h
  · exact Or.inr (h.trans hF)

end CFSG.Quasithin.A313
end
