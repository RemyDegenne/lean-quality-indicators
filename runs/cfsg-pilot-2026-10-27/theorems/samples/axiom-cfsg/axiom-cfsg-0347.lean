public section

namespace CFSG.Quasithin.B42F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Ree.LargeReeInvolution

variable {m : ℕ}
  {K : Type} [Field K] [Finite K] [CharP K F4.prime]

theorem pureZ_map_conj {E : Subgroup (ModGL F4.tag K)} {b : ModGL F4.tag K}
    (hb : b ∈ F4.reeGamma K m) (hcomm : ∀ a ∈ E, ∀ c ∈ E, a * c = c * a)
    (hsq : ∀ a ∈ E, a ^ 2 = 1) (hpure : ∀ g ∈ E, g ≠ 1 → IsZConj m K g) :
    Nat.card (E.map (MulAut.conj b).toMonoidHom) = Nat.card E ∧
    (∀ a ∈ E.map (MulAut.conj b).toMonoidHom, ∀ c ∈ E.map (MulAut.conj b).toMonoidHom,
      a * c = c * a) ∧
    (∀ a ∈ E.map (MulAut.conj b).toMonoidHom, a ^ 2 = 1) ∧
    (∀ g ∈ E.map (MulAut.conj b).toMonoidHom, g ≠ 1 → IsZConj m K g) := by
  refine ⟨Subgroup.card_map_of_injective (MulAut.conj b).injective, ?_, ?_, ?_⟩
  · intro y hy y' hy'
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    obtain ⟨e', he', rfl⟩ := mem_map_conj.1 hy'
    calc b * e * b⁻¹ * (b * e' * b⁻¹) = b * (e * e') * b⁻¹ := by group
      _ = b * (e' * e) * b⁻¹ := by rw [hcomm e he e' he']
      _ = b * e' * b⁻¹ * (b * e * b⁻¹) := by group
  · intro y hy
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    exact conj_sq_eq_one (hsq e he)
  · intro y hy hy1
    obtain ⟨e, he, rfl⟩ := mem_map_conj.1 hy
    refine (hpure e he fun h1 => hy1 ?_).conj hb
    rw [h1]
    group

end CFSG.Quasithin.B42F4
end
