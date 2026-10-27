@[expose] public noncomputable section

open CategoryTheory

open scoped MonoidAlgebra

namespace CategoryTheory

universe v u

variable (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]

open Finsupp

namespace Free

attribute [local simp] single_comp_single

variable {C} {D : Type u} [Category.{v} D] [Preadditive D] [Linear R D]

open Preadditive Linear

set_option backward.isDefEq.respectTransparency false in
/-- Two `R`-linear functors out of the `R`-linear completion are isomorphic iff their
compositions with the embedding functor are isomorphic.
-/
def ext {F G : Free R C ⥤ D} [F.Additive] [F.Linear R] [G.Additive] [G.Linear R]
    (α : embedding R C ⋙ F ≅ embedding R C ⋙ G) : F ≅ G :=
  NatIso.ofComponents (fun X => α.app X)
    (by
      intro X Y f
      induction f using Finsupp.induction_linear with
      | zero => simp
      | add f₁ f₂ w₁ w₂ =>
        rw [Functor.map_add, add_comp, w₁, w₂, Functor.map_add, comp_add]
      | single f' r =>
        rw [Iso.app_hom, Iso.app_hom, ← smul_single_one, F.map_smul, G.map_smul, smul_comp,
          comp_smul]
        change r • (embedding R C ⋙ F).map f' ≫ _ = r • _ ≫ (embedding R C ⋙ G).map f'
        rw [α.hom.naturality f'])

end Free
end CategoryTheory
end
