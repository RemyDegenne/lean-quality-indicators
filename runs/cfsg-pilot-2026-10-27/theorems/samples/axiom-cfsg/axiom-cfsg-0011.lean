public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggTPJData_of_layer {L' R : Type} [Group L'] [Finite L'] [Group R] (ψ : L' →* R)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center L')) {c : MulAut L'}
    (hc : ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (c l)) {ER : Subgroup R}
    (hER : GGLayerOf (ggRFix ψ {c}) ER) {X : Type} [Group X] (e : ER ≃* X)
    (hX : Subgroup.center X = ⊥) (h3 : 3 ∣ Nat.card X) {J : Subgroup L'}
    (hJ : IsComponentOf J (ggFix c)) :
    Nonempty (J ⧸ Subgroup.center J ≃* X) ∧ ¬ 3 ∣ Nat.card (Subgroup.center J) ∧
      3 ∣ Nat.card J := by
  have hF : ∀ f ∈ ({c} : Set (MulAut L')), ∃ φ : MulAut R, ∀ l, φ (ψ l) = ψ (f l) := by
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact hc
  have hC : ∀ l, l ∈ ggFix c ↔ ∀ f ∈ ({c} : Set (MulAut L')), f l = l := by
    intro l
    rw [mem_ggFix]
    constructor
    · intro h f hf
      rw [Set.mem_singleton_iff] at hf
      subst hf
      exact h
    · intro h
      exact h c (Set.mem_singleton c)
  obtain ⟨E, hEcomp, huniq, hmax, hmap⟩ :=
    ggLayerOf_lift ψ hψ hker ({c} : Set (MulAut L')) hF (ggFix c) hC hER
  have hJE : J = E := huniq J hJ
  have hmapJ : J.map ψ = ER := by rw [hJE, hmap]
  have hmem : ∀ j : J, ψ (j : L') ∈ ER := fun j => by
    rw [← hmapJ]
    exact Subgroup.mem_map.mpr ⟨(j : L'), j.2, rfl⟩
  let φJ : J →* ER :=
    { toFun := fun j => ⟨ψ (j : L'), hmem j⟩
      map_one' := Subtype.ext (map_one ψ)
      map_mul' := fun x y => Subtype.ext (map_mul ψ (x : L') (y : L')) }
  have φJ_apply : ∀ j : J, (φJ j : R) = ψ (j : L') := fun j => rfl
  have hφJsurj : Function.Surjective φJ := by
    intro r
    obtain ⟨j, hj, hjr⟩ := Subgroup.mem_map.mp (by rw [hmapJ]; exact r.2)
    exact ⟨⟨j, hj⟩, Subtype.ext hjr⟩
  have hcenterER : Subgroup.center ER = ⊥ := by
    apply le_antisymm
    · intro z hz
      rw [Subgroup.mem_bot]
      have hz' : (e z : X) ∈ Subgroup.center X := by
        rw [Subgroup.mem_center_iff]
        intro x
        obtain ⟨w, rfl⟩ := e.surjective x
        rw [← map_mul, ← map_mul]
        exact congrArg e (Subgroup.mem_center_iff.mp hz w)
      rw [hX] at hz'
      have h1 : e z = 1 := by simpa using hz'
      exact e.injective (by rw [h1, map_one])
    · exact bot_le
  have hker_center : φJ.ker = Subgroup.center J := by
    ext j
    constructor
    · intro hj
      rw [Subgroup.mem_center_iff]
      intro k
      have h1 : ψ (j : L') = 1 := by
        rw [← φJ_apply j]
        exact congrArg Subtype.val (MonoidHom.mem_ker.mp hj)
      have hz : (j : L') ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr h1)
      apply Subtype.ext
      simpa using Subgroup.mem_center_iff.mp hz (k : L')
    · intro hj
      apply MonoidHom.mem_ker.mpr
      have hzER : φJ j ∈ Subgroup.center ER := by
        rw [Subgroup.mem_center_iff]
        intro r
        obtain ⟨k, rfl⟩ := hφJsurj r
        rw [← map_mul, ← map_mul]
        exact congrArg φJ (Subgroup.mem_center_iff.mp hj k)
      have hbot : φJ j ∈ (⊥ : Subgroup ER) := hcenterER ▸ hzER
      simpa using hbot
  have hZJ : (Subgroup.center J).map J.subtype ≤ Subgroup.center L' := by
    rintro x ⟨j, hj, rfl⟩
    have hj' : j ∈ φJ.ker := hker_center.symm ▸ hj
    have h1 : ψ (j : L') = 1 := by
      rw [← φJ_apply j]
      exact congrArg Subtype.val (MonoidHom.mem_ker.mp hj')
    exact hker (MonoidHom.mem_ker.mpr h1)
  have hcardZ : Nat.card (Subgroup.center J) ∣ Nat.card (Subgroup.center L') := by
    have hmap' : Nat.card ((Subgroup.center J).map J.subtype) =
        Nat.card (Subgroup.center J) :=
      Subgroup.card_map_of_injective (f := J.subtype) (Subgroup.subtype_injective J)
    rw [← hmap']
    exact Subgroup.card_dvd_of_le hZJ
  refine ⟨?_, ?_, ?_⟩
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hker_center).symm.trans
      ((QuotientGroup.quotientKerEquivOfSurjective φJ hφJsurj).trans e)⟩
  · intro h3J
    exact hZ (h3J.trans hcardZ)
  · have hcardERJ : Nat.card ER ∣ Nat.card J :=
      Subgroup.card_dvd_of_surjective (f := φJ) hφJsurj
    have hcardXER : Nat.card X = Nat.card ER := Nat.card_congr e.symm.toEquiv
    exact (hcardXER ▸ h3).trans hcardERJ

end CFSG.StandardType
end
