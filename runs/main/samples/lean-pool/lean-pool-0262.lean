@[expose] public section

namespace VirasoroProject

section LieTwoCocycle.CentralExtension

universe u

variable {𝕜 : Type u} [CommRing 𝕜]

variable {𝓰 𝓪 : Type u} [LieRing 𝓰] [LieAlgebra 𝕜 𝓰] [LieRing 𝓪] [LieAlgebra 𝕜 𝓪]

variable (γ : LieTwoCocycle 𝕜 𝓰 𝓪)

namespace LieTwoCocycle.CentralExtension

lemma _root_.VirasoroProject.LieTwoCocycle.CentralExtension.range_emb_eq_ker_proj [IsLieAbelian 𝓪] :
    (LieTwoCocycle.CentralExtension.emb γ).range = (LieTwoCocycle.CentralExtension.proj γ).ker := by
  ext Z
  change Z ∈ (LieTwoCocycle.CentralExtension.emb γ).range
        ↔ Z ∈ (LieTwoCocycle.CentralExtension.proj γ).ker
  rw [mem_range_emb_iff, mem_ker_proj_iff]

end LieTwoCocycle.CentralExtension
end LieTwoCocycle.CentralExtension
end VirasoroProject
end
