public section

namespace CFSG.CGT.Hall82.Setting

open CFSG CFSG.QuasithinUnique CFSG.CGT.Hall82 CFSG.ComponentClassification.AS81

open CFSG.ComponentClassification.AS81.Hexa

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M L : Subgroup G} {R : Subgroup G}
  {rep : Fin 64 → G} {Q : Subgroup G} {S : Setting G M L}

theorem exists_normal_of_split (S : Setting G M L)
    (hF : ModelFacts) (hD : DModelFacts)
    (hc : HexaCoord (blockU L) R (hallPts (blockU L) L) rep)
    (hC1 : Subgroup.centralizer (L : Set G) = ⊥)
    (Φ : ↥M →* Equiv.Perm (Fin 64)) (hΦinj : Function.Injective Φ)
    (hΦ : ∀ m : ↥M, ∃ a : Fin 64, Φ m = transl a * S.psiM hc m)
    (hΦrep : ∀ (m : ↥M) (b : Fin 64), (m : G) = rep b → Φ m = transl b)
    {Q : Subgroup G} (hQM : Q ≤ M) (hQc : Q ≤ Subgroup.centralizer ({rep 5} : Set G))
    (hQn : ∀ g ∈ Subgroup.centralizer ({rep 5} : Set G), ∀ q ∈ Q, g * q * g⁻¹ ∈ Q)
    (hQV : ∀ v, rep v ∈ Q ↔ InHallU v) (hψQ : S.psiSub hc Q = hallRM)
    (hψM : S.psiSub hc M = hexaM)
    (hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b * a⁻¹ * b⁻¹ = 1 ∨ a * b * a⁻¹ * b⁻¹ = rep 5)
    (hQsq : ∀ a ∈ Q, a * a = 1 ∨ a * a = rep 5)
    (h34 : ∀ (g : G) (h h' : Fin 64), IsOvalVec h → IsOvalVec h' →
      g * rep h * g⁻¹ = rep h' → g ∈ M) :
    ∃ A : Subgroup G, A ≤ Q ∧ rep 5 ∈ A ∧ Nat.card A = 16 ∧
      ∀ g ∈ Subgroup.centralizer ({rep 5} : Set G), ∀ a ∈ A, g * a * g⁻¹ ∈ A := by
  let H : Hyp S R rep Q :=
    { hF := hF, hD := hD, hc := hc, hC1 := hC1, Φ := Φ, hΦinj := hΦinj,
      hΦ := hΦ, hΦrep := hΦrep, hQM := hQM, hQc := hQc, hQn := hQn,
      hQV := hQV, hψQ := hψQ, hψM := hψM, hQcomm := hQcomm, hQsq := hQsq, h34 := h34 }
  exact ⟨Hyp.A H, Hyp.A_le_Q H, Hyp.c_mem_A H, Hyp.card_A H,
    fun g hg a ha => Hyp.A_normalized H hg ha⟩

end CFSG.CGT.Hall82.Setting
end
