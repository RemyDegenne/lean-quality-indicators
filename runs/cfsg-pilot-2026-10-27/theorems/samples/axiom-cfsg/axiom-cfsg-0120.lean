open CFSG

open scoped Pointwise commutatorElement

public lemma CFSG.centralizer_subgroupOf_normalizer_eq {G : Type*} [Group G] (R : Subgroup G) :
    Subgroup.centralizer ((R.subgroupOf (Subgroup.normalizer R)) : Set (Subgroup.normalizer (R : Set G))) =
      (Subgroup.centralizer (R : Set G)).subgroupOf (Subgroup.normalizer (R : Set G)) := by
  let N : Subgroup G := Subgroup.normalizer R
  ext x
  constructor
  · intro hx
    change (x : G) ∈ Subgroup.centralizer (R : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    let yN : N := ⟨y, (Subgroup.le_normalizer (H := R)) hy⟩
    have hyN : yN ∈ R.subgroupOf N := hy
    have hcomm := (Subgroup.mem_centralizer_iff.mp hx) yN hyN
    exact congrArg Subtype.val hcomm
  · intro hx
    change (x : G) ∈ Subgroup.centralizer (R : Set G) at hx
    rw [Subgroup.mem_centralizer_iff] at hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    apply Subtype.ext
    exact hx (y : G) hy
