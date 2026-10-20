@[expose] public section

namespace LO

namespace FirstOrder

namespace Completeness

open Semiformula Encodable _root_.LO.FirstOrder.Entailment

variable {L : Language.{u}}

variable {T : Theory L} {Γ : Sequent L}

local notation:25 Δ₁" ≺[" c:25 "] " Δ₂:80 => Redux T c Δ₁ Δ₂

variable [∀ k, DecidableEq (L.Func k)] [∀ k, DecidableEq (L.Rel k)] [∀ k,
  Encodable (L.Func k)] [∀ k, Encodable (L.Rel k)]

local notation:25 Δ₁" ≺⟨" s:25 "⟩ " Δ₂:80 => ReduxNat T s Δ₁ Δ₂

section «lp_section_2»

local notation "chainAt[" s "]" => chain T Γ s

local notation "chainAll" => chainSet T Γ

omit [(k : ℕ) → DecidableEq (L.Func k)] [(k : ℕ) → DecidableEq (L.Rel k)] in
lemma chain_monotone (nwf : ¬WellFounded (SearchTree.Lt T Γ)) {s u : ℕ} (h : s ≤ u) :
    chainAt[s] ⊆ chainAt[u] := by
  suffices ∀ d, chainAt[s] ⊆ chainAt[s + d] by
    simpa[Nat.add_sub_of_le h] using this (u - s)
  intro d
  induction d with
  | zero => simp
  | succ d ih =>
    simpa only [Nat.add_succ] using Collection.subset_trans ih <|
      ReduxNat.antimonotone (chain_spec nwf (s + d))

end «lp_section_2»
end Completeness
end FirstOrder
end LO
end
