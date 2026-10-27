public section

namespace CFSG.Quasithin.S146zU.UG1

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7

open scoped Pointwise commutatorElement

attribute [local instance] commGroupOfFact

section Gen

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem dmod_swap (h : HypF918 T V L V₁ Vp H K) {Ka Kb : Subgroup G}
    (hcomm : ∀ (a b : ↥H), (a : G) ∈ Ka → (b : G) ∈ Kb →
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a *
          actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b =
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b *
          actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a)
    (hD : ∀ (a b : ↥H), (a : G) ∈ Ka → (b : G) ∈ Kb → ∀ y : ↥(tildeOf V₁ (conjClosure Vp H)),
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b
          (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹) =
        actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a y * y⁻¹)
    (b a : ↥H) (hb : (b : G) ∈ Kb) (ha : (a : G) ∈ Ka)
    (y : ↥(tildeOf V₁ (conjClosure Vp H))) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) a
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b y * y⁻¹) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure Vp H) b y * y⁻¹ := by
  have : Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure Vp H))) :=
    ⟨h.toHypF98.toHypF91.isElemAbelian_tilde⟩
  exact fix_swap (hcomm a b ha hb).symm (hD a b ha hb) y

end Gen
end CFSG.Quasithin.S146zU.UG1
end
