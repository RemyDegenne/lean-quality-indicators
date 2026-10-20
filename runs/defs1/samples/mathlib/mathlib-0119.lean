@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits SimplexCategory
  SimplicialObject Opposite CategoryTheory.Idempotents

open scoped Simplicial DoldKan

namespace AlgebraicTopology

namespace DoldKan

variable {C : Type*} [Category* C] [Preadditive C] (K K' : ChainComplex C ℕ) (f : K ⟶ K')
  {Δ Δ' Δ'' : SimplexCategory}

namespace Γ₀

variable [HasFiniteCoproducts C]

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
/-- By construction, the simplicial `Γ₀.obj K` is equipped with a splitting. -/
def splitting (K : ChainComplex C ℕ) : SimplicialObject.Splitting (Γ₀.obj K) where
  N n := K.X n
  ι n := Sigma.ι (Γ₀.Obj.summand K (op ⦋n⦌)) (Splitting.IndexSet.id (op ⦋n⦌))
  isColimit' Δ := IsColimit.ofIsoColimit (colimit.isColimit _) (Cofan.ext (Iso.refl _) (by
      intro A
      dsimp [Splitting.cofan']
      rw [comp_id, Γ₀.Obj.map_on_summand₀ K (SimplicialObject.Splitting.IndexSet.id A.1)
        (show A.e ≫ 𝟙 _ = A.e.op.unop ≫ 𝟙 _ by rfl), Γ₀.Obj.Termwise.mapMono_id]
      dsimp
      rw [id_comp]
      rfl))

end Γ₀
end DoldKan
end AlgebraicTopology
end
end
