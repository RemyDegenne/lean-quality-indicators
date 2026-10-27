public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G]

theorem normalizer_le_normalizer_oTwoPrime (K : Subgroup G) (p : ℕ) :
    Subgroup.normalizer (K : Set G) ≤ Subgroup.normalizer (oTwoPrime K p : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (K : Set G), ∀ x ∈ oTwoPrime K p,
      g * x * g⁻¹ ∈ oTwoPrime K p := by
    intro g hg x hx
    have hgK : ∀ a ∈ K, g * a * g⁻¹ ∈ K := fun a ha => (Subgroup.mem_normalizer_iff.mp hg a).mp ha
    have hgK' : ∀ a ∈ K, g⁻¹ * a * g ∈ K := fun a ha => by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) a).mp ha
      simpa using this
    let c : ↥K ≃* ↥K :=
      { toFun := fun a => ⟨g * a * g⁻¹, hgK a a.2⟩
        invFun := fun a => ⟨g⁻¹ * a * g, hgK' a a.2⟩
        left_inv := fun a => Subtype.ext (by simp [mul_assoc])
        right_inv := fun a => Subtype.ext (by simp [mul_assoc])
        map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
    have hc : (CFSG.pCore 2 ↥K).map c.toMonoidHom = CFSG.pCore 2 ↥K :=
      Subgroup.characteristic_iff_map_eq.mp
        (by exact CFSG.LieType.BorelTits.pCore_characteristic 2) c
    let cb := QuotientGroup.congr (CFSG.pCore 2 ↥K) (CFSG.pCore 2 ↥K) c hc
    have hX : (CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K)).map cb.toMonoidHom =
        CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) :=
      CFSG.pCore_map_iso p cb
    obtain ⟨y, hy, rfl⟩ := hx
    have hy' : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (c y) ∈
        CFSG.pCore p (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [← hX]
      exact ⟨_, hy, rfl⟩
    exact (mem_oTwoPrime_iff (c y)).mpr hy'
  intro g hg
  refine mem_normalizer_of_conj (key g hg) (fun x hx => ?_)
  have := key g⁻¹ (Subgroup.inv_mem _ hg) x hx
  simpa using this

end CFSG.Quasithin.Vol2.Ch11.SecD
end
