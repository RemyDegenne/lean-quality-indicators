public section

open CategoryTheory

open scoped Pointwise

universe w v u

namespace IsIdempotentElem

variable {A : Type u} [Ring A] {e : A} (he : IsIdempotentElem e)

/-- The unit of the corner equivalence, `M ≅ Hom_{eAe}(eA, eM)`, natural in `M`, for a full
idempotent `e`. -/
noncomputable def cornerUnitIso (hfull : TwoSidedIdeal.span {e} = ⊤) :
    𝟭 (ModuleCat.{max u v} A) ≅ he.cornerFunctor ⋙ he.cornerCoindFunctor :=
  NatIso.ofComponents (fun M ↦ (LinearEquiv.ofBijective (he.smulTopActionHom M)
    ⟨he.smulTopActionHom_injective hfull, he.smulTopActionHom_surjective hfull⟩).toModuleIso)
    fun f ↦ ModuleCat.hom_ext (LinearMap.ext fun m ↦ LinearMap.ext fun x ↦ Subtype.ext
      ((he.coe_cornerFunctor_map_hom_apply f _).trans (f.hom.map_smul x.1 m)).symm)

end IsIdempotentElem
end
