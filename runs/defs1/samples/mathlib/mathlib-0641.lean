@[expose] public section

noncomputable section

open Finset ContinuousMultilinearMap Fin Function

universe u v v' wE wE₁ wE' wEi wG wG'

variable {𝕜 : Type u} {ι : Type v} {ι' : Type v'} {n : ℕ} {E : ι → Type wE}
  {Ei : Fin n.succ → Type wEi} {G : Type wG} {G' : Type wG'} [Fintype ι]
  [Fintype ι'] [NontriviallyNormedField 𝕜] [∀ i, NormedAddCommGroup (E i)]
  [∀ i, NormedSpace 𝕜 (E i)] [∀ i, NormedAddCommGroup (Ei i)] [∀ i, NormedSpace 𝕜 (Ei i)]
  [NormedAddCommGroup G] [NormedSpace 𝕜 G] [NormedAddCommGroup G'] [NormedSpace 𝕜 G']

variable (𝕜 Ei G)

variable {𝕜 Ei G}

variable (𝕜 Ei G)

variable (n G')

variable {n 𝕜 G Ei G'}

variable (𝕜 Ei G)

variable {𝕜 Ei G}

variable (𝕜 G G')

variable {𝕜 G G'}

namespace ContinuousMultilinearMap

variable (𝕜 G G')

variable {𝕜 G G'}

section

variable (𝕜 ι ι' G G')

/-- Linear isometric equivalence between the space of continuous multilinear maps with variables
indexed by `ι ⊕ ι'` and the space of continuous multilinear maps with variables indexed by `ι`
taking values in the space of continuous multilinear maps with variables indexed by `ι'`.

The forward and inverse functions are `ContinuousMultilinearMap.currySum`
and `ContinuousMultilinearMap.uncurrySum`. Use this definition only if you need
some properties of `LinearIsometryEquiv`. -/
def currySumEquiv : ContinuousMultilinearMap 𝕜 (fun _ : ι ⊕ ι' => G) G' ≃ₗᵢ[𝕜]
    ContinuousMultilinearMap 𝕜 (fun _ : ι => G) (ContinuousMultilinearMap 𝕜 (fun _ : ι' => G) G') :=
  LinearIsometryEquiv.ofBounds
    { toFun := currySum
      invFun := uncurrySum
      map_add' := fun f g => by
        ext
        rfl
      map_smul' := fun c f => by
        ext
        rfl
      left_inv := fun f => by
        ext m
        congrm f $(Sum.elim_comp_inl_inr m) }
    (fun f => MultilinearMap.mkContinuousMultilinear_norm_le _ (norm_nonneg f) _) fun f => by
      simp only [LinearEquiv.coe_symm_mk]
      exact MultilinearMap.mkContinuous_norm_le _ (norm_nonneg f) _

end
end ContinuousMultilinearMap
end
end
