public section

namespace CFSG.QuasithinUnique.A5.Kc3L3

open Matrix CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.QuasithinUnique.A5.Kc3Irr

variable {F : Type} [Field F] [CharP F 2]

omit [CharP F 2] in
theorem finrank_mat_le_two (𝒲 : Submodule F (Matrix (Fin 3) (Fin 3) F))
    (h0 : ∀ A ∈ 𝒲, ∀ B ∈ 𝒲, A * B = 0) : Module.finrank F 𝒲 ≤ 2 := by
  have hW : Module.finrank F (Fin 3 → F) = 3 := by simp
  have h1 := Kc3Lin3.finrank_le_two hW
    (𝒲.map (Matrix.toLin' : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] _).toLinearMap) (by
      rintro _ ⟨A, hA, rfl⟩ _ ⟨B, hB, rfl⟩
      show Matrix.toLin' A ∘ₗ Matrix.toLin' B = 0
      rw [← Matrix.toLin'_mul, h0 A hA B hB]
      exact map_zero _)
  have h2 := LinearEquiv.finrank_eq ((Matrix.toLin' : Matrix (Fin 3) (Fin 3) F ≃ₗ[F] _).submoduleMap 𝒲)
  omega

end CFSG.QuasithinUnique.A5.Kc3L3
end
