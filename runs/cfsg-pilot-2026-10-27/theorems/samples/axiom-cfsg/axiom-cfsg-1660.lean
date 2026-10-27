public section

namespace CFSG.OddStandard.SmallF3.HarrisU33.S4B

open Subgroup

variable {G : Type*} [Group G] [Finite G]

theorem card_le_mul_card_centralizer {R A : Subgroup G} (hA : ∀ r ∈ R, ∀ x ∈ A, r * x * r⁻¹ ∈ A)
    {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) (hAR : A ≤ R) :
    Nat.card R ≤ (Nat.card A - 1) * Nat.card (R ⊓ centralizer ({a} : Set G) : Subgroup G) := by
  refine card_le_mul_card_orbit (H := R) a ?_
  have hsub : Set.range (fun h : R => (h : G) * a * (h : G)⁻¹) ⊆ (A : Set G) \ {1} := by
    rintro y ⟨r, rfl⟩
    refine ⟨hA r r.2 a ha, ?_⟩
    simp only [Set.mem_singleton_iff]
    intro h
    apply ha1
    have h' := congrArg (fun z : G => (r : G)⁻¹ * z * (r : G)) h
    rwa [show (r : G)⁻¹ * ((r : G) * a * (r : G)⁻¹) * (r : G) = a by group,
      show (r : G)⁻¹ * 1 * (r : G) = 1 by group] at h'
  have hAncard : Nat.card A = (A : Set G).ncard := Nat.card_coe_set_eq (A : Set G)
  calc Nat.card (Set.range fun h : R => (h : G) * a * (h : G)⁻¹)
      = (Set.range fun h : R => (h : G) * a * (h : G)⁻¹).ncard := Nat.card_coe_set_eq _
    _ ≤ ((A : Set G) \ {1}).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
    _ = (A : Set G).ncard - 1 := Set.ncard_sdiff_singleton_of_mem A.one_mem
    _ = Nat.card A - 1 := by rw [hAncard]

end CFSG.OddStandard.SmallF3.HarrisU33.S4B
end
