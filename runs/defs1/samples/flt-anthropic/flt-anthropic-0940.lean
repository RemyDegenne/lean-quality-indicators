namespace IharaLemma

namespace IdempotentSplitting

variable {B : Type} [CommRing B] (S : IdempotentSplitting B) (i : Fin S.n)

section Base

variable (𝒪 : Type) [CommRing 𝒪] [Algebra 𝒪 B]

noncomputable def cornerRingLinearEquiv :
    S.CornerRing i ≃ₗ[𝒪] ↥(cornerSubmodule (M := B) (S.e i)) where
  toFun x := ⟨x.1, by
    obtain ⟨b, hb⟩ := x.2
    refine ⟨b * S.e i, ?_⟩
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul]
    linear_combination hb⟩
  invFun x := ⟨x.1, by
    obtain ⟨y, hy⟩ := x.2
    simp only [LinearMap.smul_apply, LinearMap.id_apply, smul_eq_mul] at hy
    exact ⟨y, by linear_combination y * (S.idem i).eq + hy⟩⟩
  left_inv x := Subtype.ext rfl
  right_inv x := Subtype.ext rfl
  map_add' x y := Subtype.ext rfl
  map_smul' r x := Subtype.ext (by
    obtain ⟨b, hb⟩ := x.2
    show (S.e i * algebraMap 𝒪 B r * S.e i) * (x : B) = r • (x : B)
    rw [Algebra.smul_def]
    linear_combination (algebraMap 𝒪 B r * b * (S.e i * S.e i + S.e i)) * (S.idem i).eq
      + (algebraMap 𝒪 B r - S.e i * algebraMap 𝒪 B r * S.e i) * hb)

end Base
end IdempotentSplitting
end IharaLemma
