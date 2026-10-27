public section

namespace CFSG.GH74.Generic.BProg.B1.PilotS1

open CFSG CFSG.GH74 CFSG.GH74.GLS CFSG.GH74.Generic CFSG.GH74.Generic.BProg CFSG.Blueprint Subgroup

open CFSG.GH74.Generic.BProg.B1.PilotS5 CFSG.GH74.Generic.BProg.B1.PilotS3

open CFSG.ClassicalInvolution

open scoped MatrixGroups commutatorElement

section Three

variable {X : Type} [Group X] [Finite X] {F : Type} [Field F] [Finite F] {Y : Subgroup X} {z u : X}
  {J₁ J₂ : Subgroup X}

theorem SplitAt.isSolv2CompIn₁ (hF3 : Nat.card F = 3) (h : SplitAt F Y z u J₁ J₂) :
    IsSolv2CompIn (centralizer ({u} : Set X) ⊓ Y) J₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup X := centralizer ({u} : Set X) ⊓ Y with hH
  have hJ₁H : J₁ ≤ H := h.le₁
  set A₁ : Subgroup ↥H := J₁.subgroupOf H with hA₁
  set O : Subgroup ↥H := pPrimeCore 2 ↥H with hO
  set π : ↥H →* ↥H ⧸ O := QuotientGroup.mk' O with hπ
  obtain ⟨e₁⟩ := h.equiv₁
  have e₁' : ↥A₁ ≃* SL(2, F) := (Subgroup.subgroupOfEquivOfLe hJ₁H).trans e₁
  have hObot : pPrimeCore 2 ↥H = ⊥ := h.pPrimeCore_eq_bot_three hF3
  have hinj : ∀ m ∈ A₁, m ∈ π.ker → m = 1 := fun m _ hm => by
    rw [hπ, QuotientGroup.ker_mk'] at hm
    have hm' : m ∈ pPrimeCore 2 ↥H := hm
    rw [hObot, Subgroup.mem_bot] at hm'
    exact hm'
  obtain ⟨φ⟩ := nonempty_slEquiv_zmod_three hF3
  refine ⟨A₁.map π, (h.normal₁.map π (QuotientGroup.mk'_surjective O)).isSubnormal, ⟨?_⟩, ?_⟩
  · exact ((CFSG.ClassicalInvolution.Models.Transfer.mulEquivMap hinj).symm.trans e₁').trans φ
  · rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', hObot, sup_bot_eq, hA₁,
      Subgroup.map_subgroupOf_eq_of_le hJ₁H]

end Three
end CFSG.GH74.Generic.BProg.B1.PilotS1
end
