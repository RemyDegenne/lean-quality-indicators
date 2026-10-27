public section

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

namespace B1

theorem exists_fixed_ne_one [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {B : Subgroup (MulAut V)}
    (hB : IsPGroup 2 B) {M : Subgroup V} (hM : ∀ b ∈ B, ∀ m ∈ M, b m ∈ M) (hne : M ≠ ⊥) :
    ∃ m ∈ M, m ≠ 1 ∧ ∀ b ∈ B, b m = m := by
  let _ : MulAction B M :=
    { smul := fun b m => ⟨(b : MulAut V) m, hM b b.2 m m.2⟩
      one_smul := fun m => Subtype.ext rfl
      mul_smul := fun a b m => Subtype.ext rfl }
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hM2 : IsPGroup 2 M := (isPGroup_two_of_sq_eq_one hV).to_subgroup M
  have hdvd : 2 ∣ Nat.card M := by
    obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hM2
    have hn0 : n ≠ 0 := by
      rintro rfl
      exact hne (Subgroup.card_eq_one.mp (by simpa using hn))
    rw [hn]
    exact dvd_pow_self 2 hn0
  have h1 : (1 : M) ∈ MulAction.fixedPoints B M := fun b => Subtype.ext (map_one _)
  obtain ⟨m, hm, hne1⟩ := hB.exists_fixed_point_of_prime_dvd_card_of_fixed_point M hdvd h1
  refine ⟨m, m.2, fun h => hne1 (Subtype.ext h.symm), fun b hb => ?_⟩
  have := hm ⟨b, hb⟩
  exact congrArg Subtype.val this

end B1
end CFSG.Quasithin
end
