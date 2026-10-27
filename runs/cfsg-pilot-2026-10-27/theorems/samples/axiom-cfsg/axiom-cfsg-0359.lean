public section

namespace CFSG.GroupTheory

open Subgroup

open CFSG.Open

open scoped IsMulCommutative commutatorElement

theorem exists_eq_of_endomorphisms_of_card_pow_le
    {A : Type*} [AddCommGroup A] [Module (ZMod 2) A] [Finite A]
    (x y : A →ₗ[ZMod 2] A)
    (hx2 : ∀ z, x (x z) = 0) (hy2 : ∀ z, y (y z) = 0)
    (hxy : ∀ z, x (y z) = y (x z))
    (hfix : Nat.card ↥(LinearMap.ker x ⊓ LinearMap.ker y) ^ 4 ≤ Nat.card A)
    {a b : A} (ha : x a = 0) (hb : y b = 0) (hab : x b = y a) :
    ∃ n, x n = a ∧ y n = b := by
  classical
  have hcardC : Nat.card ↥(LinearMap.ker x ⊓ LinearMap.ker y) =
      2 ^ Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2)
      (V := ↥(LinearMap.ker x ⊓ LinearMap.ker y)), Nat.card_zmod]
  have hcardA : Nat.card A = 2 ^ Module.finrank (ZMod 2) A := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2) (V := A), Nat.card_zmod]
  have h4d : 4 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) ≤
      Module.finrank (ZMod 2) A := by
    rw [hcardC, hcardA, ← pow_mul] at hfix
    refine (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp ?_
    simpa [mul_comm] using hfix
  have hyK_range : LinearMap.range (y.domRestrict (LinearMap.ker x)) ≤
      LinearMap.ker x ⊓ LinearMap.ker y := by
    rintro _ ⟨z, rfl⟩
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · change x (y (z : A)) = 0
      rw [hxy (z : A), LinearMap.mem_ker.mp z.2, map_zero]
    · exact LinearMap.mem_ker.mpr (hy2 (z : A))
  have hker_yK : Module.finrank (ZMod 2) ↥(LinearMap.ker (y.domRestrict (LinearMap.ker x))) =
      Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    rw [LinearMap.ker_domRestrict]
    exact (Submodule.finrank_map_subtype_eq (LinearMap.ker x)
      ((LinearMap.ker y).comap (LinearMap.ker x).subtype)).symm.trans
        (by rw [Submodule.map_comap_subtype])
  have hK_le : Module.finrank (ZMod 2) ↥(LinearMap.ker x) ≤
      2 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (y.domRestrict (LinearMap.ker x))
    have hle := Submodule.finrank_mono hyK_range
    rw [hker_yK] at hrn
    omega
  have hrange_x_le_ker : LinearMap.range x ≤ LinearMap.ker x :=
    LinearMap.range_le_ker_iff.mpr (LinearMap.ext hx2)
  have hrange_x_le : Module.finrank (ZMod 2) ↥(LinearMap.range x) ≤
      Module.finrank (ZMod 2) ↥(LinearMap.ker x) := Submodule.finrank_mono hrange_x_le_ker
  have hn_le : Module.finrank (ZMod 2) A ≤
      4 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker x
    omega
  have hn_eq : Module.finrank (ZMod 2) A =
      4 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) :=
    le_antisymm hn_le h4d
  have hK_eq : Module.finrank (ZMod 2) ↥(LinearMap.ker x) =
      2 * Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker x
    omega
  have hrange_x_eq : Module.finrank (ZMod 2) ↥(LinearMap.range x) =
      Module.finrank (ZMod 2) ↥(LinearMap.ker x) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker x
    omega
  have hrange_x : LinearMap.range x = LinearMap.ker x :=
    Submodule.eq_of_le_of_finrank_eq hrange_x_le_ker hrange_x_eq
  have hrange_yK_eq : Module.finrank (ZMod 2)
      ↥(LinearMap.range (y.domRestrict (LinearMap.ker x))) =
      Module.finrank (ZMod 2) ↥(LinearMap.ker x ⊓ LinearMap.ker y) := by
    have hrn := LinearMap.finrank_range_add_finrank_ker (y.domRestrict (LinearMap.ker x))
    rw [hker_yK] at hrn
    omega
  have hrange_yK : LinearMap.range (y.domRestrict (LinearMap.ker x)) =
      LinearMap.ker x ⊓ LinearMap.ker y :=
    Submodule.eq_of_le_of_finrank_eq hyK_range hrange_yK_eq
  have ha_mem : a ∈ LinearMap.range x := by
    rw [hrange_x]
    exact LinearMap.mem_ker.mpr ha
  obtain ⟨r, hr⟩ := ha_mem
  have hb'_mem : b - y r ∈ LinearMap.ker x ⊓ LinearMap.ker y := by
    refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
    · rw [LinearMap.mem_ker, map_sub, hxy, hr, hab, sub_self]
    · rw [LinearMap.mem_ker, map_sub, hy2, hb, sub_self]
  rw [← hrange_yK] at hb'_mem
  obtain ⟨u, hu⟩ := hb'_mem
  have hu' : y (u : A) = b - y r := hu
  refine ⟨r + (u : A), ?_, ?_⟩
  · rw [map_add, hr, LinearMap.mem_ker.mp u.2, add_zero]
  · rw [map_add, hu']
    abel

end CFSG.GroupTheory
end
