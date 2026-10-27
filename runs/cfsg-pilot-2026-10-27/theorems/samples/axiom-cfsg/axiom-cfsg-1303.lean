public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.GroupTheory.SteinbergBM

open scoped commutatorElement Pointwise

namespace PlaneFactors

variable {B S : Type} [Group B] [Group S] [MulDistribMulAction B S]

variable {B S : Type} [Group B] [Group S] [MulDistribMulAction B S]

section Assembly

variable {p : ℕ} {B S : Type} [Group B] [Group S] [MulDistribMulAction B S] [Finite B] [Finite S]

theorem exists_second_factor (hp : p.Prime) (hp2 : p ≠ 2) (hB : IsElementaryAbelian p B)
    (hBcard : Nat.card B = p ^ 2) (hS : IsPGroup 2 S) {S₀ S₁ : Subgroup S}
    (hS₀inv : IsActionInvariant B S₀) (hS₁inv : IsActionInvariant B S₁) {b₁ : B} (hb₁ : b₁ ≠ 1)
    (hnot : ¬ (S₀ ⊓ Subgroup.centralizer (S₁ : Set S) ≤
      CFSG.fixedPointSubgroup (Subgroup.zpowers b₁) S)) :
    ∃ b₂ : B, b₂ ≠ 1 ∧ b₂ ∉ Subgroup.zpowers b₁ ∧ ∃ S₂ : Subgroup S,
      S₂ ≤ S₀ ⊓ Subgroup.centralizer (S₁ : Set S) ∧ (∃ x ∈ S₂, b₁ • x ≠ x) ∧
      IsActionInvariant B S₂ ∧ actionCommutator B S₂ = S₂ ∧ (∀ x ∈ S₂, b₂ • x = x) := by
  have : Fact p.Prime := ⟨hp⟩
  have := hB
  have hcommB : ∀ x y : B, x * y = y * x := fun x y => hB.is_comm.comm x y
  have hB2 := not_two_dvd_card_of_card_eq hp hp2 hBcard
  set X := S₀ ⊓ Subgroup.centralizer (S₁ : Set S) with hX
  have hXinv : IsActionInvariant B X :=
    isActionInvariant_inf hS₀inv (isActionInvariant_centralizer hS₁inv)
  obtain ⟨b₂, hb₂, hY⟩ : ∃ b₂ : B, b₂ ≠ 1 ∧ ¬ (X ⊓ CFSG.fixedPointSubgroup
      (Subgroup.zpowers b₂) S ≤ CFSG.fixedPointSubgroup (Subgroup.zpowers b₁) S) := by
    by_contra hcon
    push Not at hcon
    exact hnot (le_of_centralizers_le (p := p) (by rw [hBcard]) hXinv
      (not_dvd_card_of_isPGroup_two hp hp2 (hS.to_subgroup X)) hcon)
  set Y := X ⊓ CFSG.fixedPointSubgroup (Subgroup.zpowers b₂) S with hYdef
  have hYinv : IsActionInvariant B Y :=
    isActionInvariant_inf hXinv (isActionInvariant_fixedPointSubgroup_zpowers hcommB b₂)
  have hb₂b₁ : b₂ ∉ Subgroup.zpowers b₁ := by
    intro hmem
    apply hY
    have heq : Subgroup.zpowers b₂ = Subgroup.zpowers b₁ := zpowers_eq_of_mem hp hB hb₁ hb₂ hmem
    intro y hy
    have hb₁mem : b₁ ∈ Subgroup.zpowers b₂ := heq ▸ Subgroup.mem_zpowers b₁
    exact (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b₁ y).2 (hy.2 ⟨b₁, hb₁mem⟩)
  obtain ⟨y, hyY, hy⟩ : ∃ y ∈ Y, y ∉ CFSG.fixedPointSubgroup (Subgroup.zpowers b₁) S := by
    by_contra hcon
    push Not at hcon
    exact hY hcon
  have hy' : b₁ • y ≠ y := fun h => hy ((SolvableHall.mem_fixedPointSubgroup_zpowers_iff b₁ y).2 h)
  obtain ⟨hS₂Y, hS₂inv, hS₂c⟩ := commutator_properties hS hB2 hYinv
  refine ⟨b₂, hb₂, hb₂b₁, actionCommutator B Y, hS₂Y.trans inf_le_left, ?_, hS₂inv, hS₂c,
    fun x hx => (SolvableHall.mem_fixedPointSubgroup_zpowers_iff b₂ x).1 (hS₂Y hx).2⟩
  by_contra hcon
  push Not at hcon
  obtain ⟨d, hd, c, hcY, hc, hdc⟩ :=
    exists_mul_of_invariant_isPGroup Nat.prime_two (hS.to_subgroup Y) hB2 hYinv hyY
  apply hy'
  rw [hdc, smul_mul', hcon d hd, hc b₁]

end Assembly
end PlaneFactors
end CFSG.RankThree.PartOne
end
