public section

namespace CFSG.Quasithin.H13.U3

open CFSG.Quasithin Matrix

theorem dGL_mem_normalizer_rhoT
    : dGL ∈ Subgroup.normalizer (rhoT : Set (GL (Fin 6) (ZMod 2))) := by
  have hconj : ∀ t ∈ u33Data.T, dGL * rho6 t * dGL⁻¹ ∈ rhoT := by
    intro t ht
    let φ : U33G →* GL (Fin 6) (ZMod 2) := (MulAut.conj dGL).toMonoidHom.comp rho6
    have hφ : ∀ g, φ g = dGL * rho6 g * dGL⁻¹ := fun _ => rfl
    have hle : u33Data.T ≤ rhoT.comap φ := by
      refine (Subgroup.closure_le _).2 ?_
      intro h hh
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hh
      rw [SetLike.mem_coe, Subgroup.mem_comap, hφ]
      have hmem : ∀ w : List (Fin 5), (∀ k ∈ w, k ∈ ([0, 1, 2] : List (Fin 5))) →
          wordElem w ∈ u33Data.T := by
        intro w hw'
        refine list_prod_mem fun x hx => ?_
        obtain ⟨k, hk, rfl⟩ := List.mem_map.1 hx
        have := hw' k hk
        simp only [List.mem_cons, List.not_mem_nil, or_false] at this
        rcases this with rfl | rfl | rfl
        · exact u33Data.a_mem_T
        · exact u33Data.b_mem_T
        · exact u33Data.s_mem_T
      rcases hh with rfl | rfl | rfl
      · rw [show dGL * rho6 u33Data.a * dGL⁻¹ = rho6 (wordElem (dWords 0)) from dGL_conj 0]
        exact ⟨_, hmem _ (by decide), rfl⟩
      · rw [show dGL * rho6 u33Data.b * dGL⁻¹ = rho6 (wordElem (dWords 1)) from dGL_conj 1]
        exact ⟨_, hmem _ (by decide), rfl⟩
      · rw [show dGL * rho6 u33Data.s * dGL⁻¹ = rho6 (wordElem (dWords 2)) from dGL_conj 2]
        exact ⟨_, hmem _ (by decide), rfl⟩
    exact hle ht
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · rintro ⟨t, ht, rfl⟩
    exact hconj t ht
  · intro hh
    obtain ⟨t, ht, hth⟩ := hh
    have h1 := hconj t ht
    rw [hth, dGL_inv, ← mul_assoc, ← mul_assoc, dGL_mul_self, one_mul, mul_assoc, dGL_mul_self,
      mul_one] at h1
    exact h1

end CFSG.Quasithin.H13.U3
end
