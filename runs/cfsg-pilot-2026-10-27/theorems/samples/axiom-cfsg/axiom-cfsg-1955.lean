public section

namespace CFSG.Quasithin

open CFSG.Quasithin CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem le_of_card_four {X Y Z : Subgroup D} (hX : Nat.card X = 4) (hZ : Nat.card Z = 2)
    (hZX : Z ≤ X) (hZY : Z ≤ Y) {c : D} (hcX : c ∈ X) (hcY : c ∈ Y) (hcZ : c ∉ Z) : X ≤ Y := by
  have hK : Z ≤ X ⊓ Y := le_inf hZX hZY
  have h1 : Nat.card Z ∣ Nat.card (X ⊓ Y : Subgroup D) := Subgroup.card_dvd_of_le hK
  have h2 : Nat.card (X ⊓ Y : Subgroup D) ∣ Nat.card X :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [hZ] at h1
  rw [hX] at h2
  have hne : (X ⊓ Y : Subgroup D) ≠ Z := fun e => hcZ (by
    have : c ∈ (X ⊓ Y : Subgroup D) := ⟨hcX, hcY⟩
    rwa [e] at this)
  have hlt : Nat.card Z < Nat.card (X ⊓ Y : Subgroup D) := by
    have hle := Subgroup.card_le_of_le hK
    rcases hle.lt_or_eq with hlt | heq
    · exact hlt
    · exact absurd (Subgroup.eq_of_le_of_card_ge hK heq.symm.le).symm hne
  rw [hZ] at hlt
  have hc4 : Nat.card (X ⊓ Y : Subgroup D) = 4 := by
    have hpos : 0 < Nat.card (X ⊓ Y : Subgroup D) := Nat.card_pos
    have hle : Nat.card (X ⊓ Y : Subgroup D) ≤ 4 := Nat.le_of_dvd (by norm_num) h2
    interval_cases k : Nat.card (X ⊓ Y : Subgroup D) <;> omega
  have heq : X ⊓ Y = X := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hc4, hX])
  rw [← heq]
  exact inf_le_right

end GoldAmL3
end F6
end CFSG.Quasithin
end
