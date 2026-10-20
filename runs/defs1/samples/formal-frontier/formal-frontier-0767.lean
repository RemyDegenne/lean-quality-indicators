public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- The map of the degree-zero cokernels induced by a map of short
complexes. -/
@[expose] noncomputable def covariantCokernelMap {S₁ S₂ : ShortComplex C}
    (f : S₁ ⟶ S₂) (X : C) :
    cokernel (AddCommGrpCat.ofHom
      ((mk₀ S₁.g).postcomp X (add_zero 0))) ⟶
        cokernel (AddCommGrpCat.ofHom
          ((mk₀ S₂.g).postcomp X (add_zero 0))) :=
  cokernel.map _ _
    (AddCommGrpCat.ofHom ((mk₀ f.τ₂).postcomp X (add_zero 0)))
    (AddCommGrpCat.ofHom ((mk₀ f.τ₃).postcomp X (add_zero 0))) (by
      ext x
      change (x.comp (mk₀ S₁.g) (add_zero 0)).comp
          (mk₀ f.τ₃) (add_zero 0) =
        (x.comp (mk₀ f.τ₂) (add_zero 0)).comp
          (mk₀ S₂.g) (add_zero 0)
      rw [comp_assoc_of_second_deg_zero, comp_assoc_of_second_deg_zero,
        mk₀_comp_mk₀, mk₀_comp_mk₀, f.comm₂₃])

end CategoryTheory.Abelian.Ext
end
end
