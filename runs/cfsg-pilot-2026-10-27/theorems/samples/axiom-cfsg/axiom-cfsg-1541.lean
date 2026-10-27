public section

namespace CFSG.CGT.PushingUpLit.A78Sp4

open CFSG.ABGLocalTools

variable {G : Type} [Group G]

theorem exists_fixed_conj_of_not_dvd {p : ℕ} [Fact p.Prime] [Finite G] {T : Subgroup G}
    (hT : IsPGroup p T) {X : Set G} (hX : ∀ t ∈ T, ∀ x ∈ X, t * x * t⁻¹ ∈ X)
    (hp : ¬ p ∣ Nat.card X) : ∃ x ∈ X, ∀ t ∈ T, t * x * t⁻¹ = x := by
  let _ : MulAction T X :=
    { smul := fun t x => ⟨(t : G) * x * (t : G)⁻¹, hX t t.2 x x.2⟩
      one_smul := fun x => Subtype.ext (by
        change ((1 : T) : G) * x * ((1 : T) : G)⁻¹ = x
        simp)
      mul_smul := fun s t x => Subtype.ext (by
        change ((s * t : T) : G) * x * ((s * t : T) : G)⁻¹ =
          (s : G) * ((t : G) * x * (t : G)⁻¹) * (s : G)⁻¹
        simp [mul_assoc]) }
  obtain ⟨x, hx⟩ := hT.nonempty_fixed_point_of_prime_not_dvd_card X hp
  exact ⟨x, x.2, fun t ht => congrArg Subtype.val (MulAction.mem_fixedPoints.1 hx ⟨t, ht⟩)⟩

end CFSG.CGT.PushingUpLit.A78Sp4
end
