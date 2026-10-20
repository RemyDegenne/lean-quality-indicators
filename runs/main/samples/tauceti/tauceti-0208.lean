public section

open Subgroup

namespace DoubleCoset

variable {G K : Type*} [Group G] [Group K]

@[simp] lemma mem_doubleCoset_map_equiv_iff (e : G ≃* K) (H₁ H₂ : Subgroup G) (g x : G) :
    e x ∈ doubleCoset (e g) (e '' (H₁ : Set G)) (e '' (H₂ : Set G)) ↔
      x ∈ doubleCoset g H₁ H₂ := by
  constructor
  · intro hx
    obtain ⟨a, ha, b, hb, hab⟩ := mem_doubleCoset.mp hx
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    refine mem_doubleCoset.mpr ⟨a', ha', b', hb', e.injective ?_⟩
    rw [map_mul, map_mul]
    exact hab
  · intro hx
    obtain ⟨a, ha, b, hb, rfl⟩ := mem_doubleCoset.mp hx
    exact mem_doubleCoset.mpr ⟨e a, ⟨a, ha, rfl⟩,
      e b, ⟨b, hb, rfl⟩, by simp only [map_mul]⟩

end DoubleCoset
end
