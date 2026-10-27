public section

namespace CFSG

namespace FiveTransitive.Degree24

open MulAction SubMulAction Subgroup

open scoped Pointwise

theorem fixingSubgroup_eq_of_range_subset_fixedPoints
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ q : P, ∀ i, q • a i = b i)
    (s : Set X) (hs : s.ncard = 5)
    (e : Fin 5 ↪ X)
    (he :
      Set.range e ⊆
        MulAction.fixedPoints
          (fixingSubgroup P s) X) :
    fixingSubgroup P (Set.range e) =
      fixingSubgroup P s := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  letI : Fintype s := Fintype.ofFinite s
  have hsCard : Fintype.card s = 5 := by
    rw [← Nat.card_eq_fintype_card,
      Nat.card_coe_set_eq, hs]
  let es : s ≃ Fin 5 :=
    Fintype.equivFinOfCardEq hsCard
  let e₀ : Fin 5 ↪ X := {
    toFun := fun i => (es.symm i).1
    inj' := by
      intro i j hij
      apply es.symm.injective
      exact Subtype.ext hij }
  have he₀Range : Set.range e₀ = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (es.symm i).2
    · intro hx
      obtain ⟨i, hi⟩ :=
        es.symm.surjective ⟨x, hx⟩
      exact ⟨i, congrArg Subtype.val hi⟩
  obtain ⟨q, hq⟩ := hP5.exists_smul_eq e₀ e
  have hrange :
      q • Set.range e₀ = Set.range e := by
    rw [Degree24.smul_range_fiveEmbedding]
    exact congrArg
      (fun z : Fin 5 ↪ X => Set.range z) hq
  let ψ :
      fixingSubgroup P (Set.range e₀) ≃*
        fixingSubgroup P (Set.range e) :=
    fixingSubgroupEquivFixingSubgroup hrange
  have hcardEq :
      Nat.card (fixingSubgroup P (Set.range e)) =
        Nat.card H := by
    calc
      Nat.card (fixingSubgroup P (Set.range e)) =
          Nat.card (fixingSubgroup P (Set.range e₀)) :=
        Nat.card_congr ψ.symm.toEquiv
      _ = Nat.card H := by rw [he₀Range]
  have hle : H ≤ fixingSubgroup P (Set.range e) := by
    intro u hu
    rw [mem_fixingSubgroup_iff]
    intro x hx
    have hxFixed := he hx
    rw [MulAction.mem_fixedPoints] at hxFixed
    exact hxFixed ⟨u, hu⟩
  exact
    (Subgroup.eq_of_le_of_card_ge hle
      (by rw [hcardEq])).symm

end FiveTransitive.Degree24
end CFSG
end
