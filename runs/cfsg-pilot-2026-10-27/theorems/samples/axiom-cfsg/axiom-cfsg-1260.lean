public section

namespace CFSG.AGLEmbeddingD2.GN

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B2F CFSG.Quasithin.E2 Equiv
  Equiv.Perm

variable {N : ℕ}

section Emb

variable {A : Type*} [Group A] (L : Subgroup A) (θ : ↥L ≃* Perm (Fin N))

variable {L θ}

theorem mem_normalizer_map_embL [Finite A] {x : A} (hx : x ∈ L) {B : Subgroup (Perm (Fin N))}
    (hxB : θ ⟨x, hx⟩ ∈ Subgroup.normalizer (B : Set (Perm (Fin N)))) :
    x ∈ Subgroup.normalizer ((B.map (embL L θ) : Subgroup A) : Set A) := by
  refine Subgroup.mem_normalizer_fintype fun n hn => ?_
  obtain ⟨b, hb, rfl⟩ := hn
  refine ⟨θ ⟨x, hx⟩ * b * (θ ⟨x, hx⟩)⁻¹, (Subgroup.mem_normalizer_iff.1 hxB b).1 hb, ?_⟩
  rw [map_mul, map_mul, map_inv, embL_theta]

end Emb
end CFSG.AGLEmbeddingD2.GN
end
