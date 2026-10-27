public section

namespace CFSG.OddTranspositions

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld.Bridge.Asc72 CFSG.OddTranspositions.QZ

variable {G : Type} [Group G] [Finite G] {D : Set G}

section SimpleNormal

variable {M K : Subgroup G} [hMn : M.Normal]

omit [Finite G] in
theorem solvable_normal_eq_bot_of_le (hMK : M ≤ K) (hMs : IsSimpleGroup M)
    (hC : Subgroup.centralizer (M : Set G) = ⊥) (hM1 : M ≠ ⊥) :
    ∀ N : Subgroup K, N.Normal → Group.IsSolvable N → N = ⊥ := by
  intro N hN hNs
  let N' : Subgroup G := N.map K.subtype
  have hN'mem : ∀ m ∈ M, ∀ x ∈ N', m * x * m⁻¹ ∈ N' := by
    intro m hm x hx
    obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hx
    exact Subgroup.mem_map.mpr ⟨⟨m, hMK hm⟩ * n * (⟨m, hMK hm⟩ : K)⁻¹,
      hN.conj_mem n hn _, by simp⟩
  let P : Subgroup M := N'.subgroupOf M
  have hP : P.Normal :=
    ⟨fun p hp m => Subgroup.mem_subgroupOf.mpr (by
      simpa using hN'mem m m.2 p (Subgroup.mem_subgroupOf.mp hp))⟩
  have hN's : Group.IsSolvable N' :=
    Group.isSolvable_of_isSolvable_injective
      (f := (N.equivMapOfInjective K.subtype K.subtype_injective).symm.toMonoidHom)
      (MulEquiv.injective _)
  let f : P →* N' :=
    { toFun := fun p => ⟨((p : M) : G), Subgroup.mem_subgroupOf.mp p.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hPs : Group.IsSolvable P :=
    Group.isSolvable_of_isSolvable_injective (f := f)
      (fun a b h => by
        have h' := congrArg (fun y : N' => (y : G)) h
        exact Subtype.ext (Subtype.ext h'))
  have hPbot : P = ⊥ := by
    have := hP
    rcases hMs.eq_bot_or_eq_top_of_normal P with h | h
    · exact h
    · exfalso
      have hMsolv : Group.IsSolvable M := by
        rw [h] at hPs
        exact Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.topEquiv : (⊤ : Subgroup M) ≃* M).symm.toMonoidHom)
          (MulEquiv.injective _)
      exact not_commute_of_centralizer_eq_bot hC hM1
        (IsSimpleGroup.comm_iff_isSolvable.mpr hMsolv)
  have hle : N' ≤ Subgroup.centralizer (M : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have hcM : x * m * x⁻¹ * m⁻¹ ∈ M :=
      M.mul_mem (hMn.conj_mem m hm x) (M.inv_mem hm)
    have hcN : x * m * x⁻¹ * m⁻¹ ∈ N' := by
      have h1 := hN'mem m hm x⁻¹ (N'.inv_mem hx)
      have h2 : x * (m * x⁻¹ * m⁻¹) ∈ N' := N'.mul_mem hx h1
      simpa [mul_assoc] using h2
    have hc1 : (⟨_, hcM⟩ : M) ∈ P := Subgroup.mem_subgroupOf.mpr hcN
    rw [hPbot, Subgroup.mem_bot] at hc1
    have hc : x * m * x⁻¹ * m⁻¹ = 1 := congrArg Subtype.val hc1
    have : x * m = m * x := by
      have := mul_inv_eq_one.mp hc
      calc x * m = x * m * x⁻¹ * x := by group
        _ = m * x := by rw [this]
    exact this.symm
  rw [hC] at hle
  rw [eq_bot_iff]
  intro n hn
  have : (n : G) ∈ N' := Subgroup.mem_map.mpr ⟨n, hn, rfl⟩
  have h1 : (n : G) = 1 := Subgroup.mem_bot.mp (hle this)
  exact Subgroup.mem_bot.mpr (Subtype.ext h1)

end SimpleNormal
end CFSG.OddTranspositions
end
