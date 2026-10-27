public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.Literature.FSmith

open Subgroup QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions

open scoped commutatorElement

theorem fsmith_theorem_two {G : Type*} [Group G] [Finite G] [IsSimpleGroup G]
    (hG : ∃ x y : G, x * y ≠ y * x) {z : G} (hz : orderOf z = 2)
    {Q : Subgroup (centralizer ({z} : Set G))}
    (hQF : Q = generalizedFitting (centralizer ({z} : Set G))) (hQ : IsExtraspecialPGroup 2 Q)
    {w : ℕ} (hcard : Nat.card Q = 2 ^ (1 + 2 * w)) (hw : 3 ≤ w)
    [Module (ZMod 2) (Additive (Abelianization Q))] (hQn : Q.Normal)
    (hΩ : _root_.commutator (TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hQ)) ≤
      (extraspecialConjOrth hQ hQn).range) :
    (∀ (m : centralizer ({z} : Set G)) (v : Additive (Abelianization Q)),
      extraspecialQuadForm hQ v = 1 →
      ¬ ∀ u, ((extraspecialConjOrth hQ hQn m :
          TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hQ)) :
          Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) u =
        u + polar (extraspecialQuadForm hQ) u v • v) ∧
    (extraspecialConjOrth hQ hQn).range =
      _root_.commutator (TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hQ)) := by
  classical
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hz2 : z * z = 1 := by rw [← pow_two, ← hz, pow_orderOf_eq_one]
  have hCQ : centralizer (Q : Set (centralizer ({z} : Set G))) ≤ Q := by
    rw [hQF]
    exact centralizer_generalizedFitting_le _
  set z₀ : centralizer ({z} : Set G) := ⟨z, mem_centralizer_singleton_iff.mpr rfl⟩ with hz₀def
  have hz₀ : ∀ g : centralizer ({z} : Set G), g * z₀ = z₀ * g := fun g =>
    Subtype.ext (mem_centralizer_singleton_iff.mp g.2)
  have hz₀1 : z₀ ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz₀Q : z₀ ∈ Q := hCQ (mem_centralizer_iff.mpr fun g _ => hz₀ g)
  have : Module.Finite (ZMod 2) (Additive (Abelianization Q)) := Module.Finite.of_finite
  have hcardV : Nat.card (Additive (Abelianization Q)) = 2 ^ (2 * w) := by
    have h2 : Nat.card (commutator Q) = 2 := by
      rw [hQ.2.1]
      exact hQ.2.2.2
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (commutator Q)
    rw [h2, hcard, pow_add, pow_one] at h1
    have h3 : Nat.card (Additive (Abelianization Q)) = Nat.card (Q ⧸ commutator Q) :=
      Nat.card_congr Additive.toMul
    rw [h3]
    omega
  have hdim : Module.finrank (ZMod 2) (Additive (Abelianization Q)) = 2 * w := by
    have h4 := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := Additive (Abelianization Q))
    rw [hcardV, Nat.card_zmod] at h4
    exact (Nat.pow_right_injective le_rfl h4).symm
  have hnd := extraspecialQuadForm_nondegenerate hQ
  have hno : ∀ (m : centralizer ({z} : Set G)) (v : Additive (Abelianization Q)),
      extraspecialQuadForm hQ v = 1 →
      ¬ ∀ u, ((extraspecialConjOrth hQ hQn m :
          TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hQ)) :
          Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) u =
        u + polar (extraspecialQuadForm hQ) u v • v := by
    intro m v hv hm
    obtain ⟨a, F, ha, haa, haF, hz₀F, hF2, hCF, hFa, he, hc⟩ :=
      exists_smith_subgroup hQ hQn hz₀ hz₀1 hz₀Q hCQ (by omega) hv hm
    let ϕ : centralizer ({z} : Set G) →* Multiplicative (ZMod 2) :=
      (dicksonHom (extraspecialQuadForm hQ) hnd).comp (extraspecialConjOrth hQ hQn)
    have hV : ∀ g : G, ϕ.transfer g = 1 := by
      have := (ϕ.transfer).normal_ker
      rcases Subgroup.Normal.eq_bot_or_eq_top (ϕ.transfer).ker with h | h
      · exfalso
        obtain ⟨x, y, hxy⟩ := hG
        apply hxy
        apply (MonoidHom.ker_eq_bot_iff _).mp h
        rw [map_mul, map_mul, mul_comm]
      · intro g
        have hg : g ∈ (ϕ.transfer).ker := by
          rw [h]
          exact mem_top g
        exact hg
    have hϕa : ϕ a ≠ 1 := by
      have hρa : ((extraspecialConjOrth hQ hQn a :
          TauCeti.QuadraticMap.orthogonalGroup (extraspecialQuadForm hQ)) :
          Additive (Abelianization Q) ≃ₗ[ZMod 2] Additive (Abelianization Q)) =
          reflect (extraspecialQuadForm hQ) v := eq_reflect_of_apply hv ha
      change dicksonHom (extraspecialQuadForm hQ) hnd (extraspecialConjOrth hQ hQn a) ≠ 1
      rw [dicksonHom_apply, hρa, finrank_commSpace_reflect hnd hv, Nat.cast_one, Ne,
        ofAdd_eq_one]
      exact one_ne_zero
    refine smith_transfer ϕ hz1 hz2 (F := F.map (centralizer ({z} : Set G)).subtype)
      (a := (a : G)) (map_subtype_le F) (hF2.map _) ?_ (mem_map_of_mem _ haF)
      (congrArg Subtype.val haa) hϕa (hV a) ?_ ?_ ?_
    · intro c hc
      have hcz : c * z = z * c := hc z (mem_map_of_mem _ hz₀F)
      have hcM : c ∈ centralizer ({z} : Set G) := mem_centralizer_singleton_iff.mpr hcz
      rcases hCF ⟨c, hcM⟩ (fun f hf => Subtype.ext (hc f (mem_map_of_mem _ hf))) with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · rintro f ⟨f', hf', rfl⟩
      rcases hFa f' hf' with h | h
      · exact Or.inl (congrArg Subtype.val h)
      · exact Or.inr (congrArg Subtype.val h)
    · obtain ⟨e, heF, he⟩ := he
      exact ⟨e, mem_map_of_mem _ heF, congrArg Subtype.val he⟩
    · obtain ⟨c₁, hc₁, c₂, hc₂, h1, h2, h3⟩ := hc
      exact ⟨c₁, mem_map_of_mem _ hc₁, c₂, mem_map_of_mem _ hc₂, congrArg Subtype.val h1,
        congrArg Subtype.val h2, congrArg Subtype.val h3⟩
  exact ⟨hno, (forall_not_transvection_iff hnd (by omega) _ hΩ).mp hno⟩

end CFSG.RankThree.Literature.FSmith
end
