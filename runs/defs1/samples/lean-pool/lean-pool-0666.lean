@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory

open scoped MonObj

universe v u

attribute [local instance] CategoryTheory.ModObj.regular

section Shift

variable {D : Type u}

/-- **The parity swap is a morphism of Γ-modules**: the two
parity swaps of `RS.RhoTwist` intertwine the four action blocks of
the Γ-module of the free module on the odd line with the four
relabelled blocks of the parity shift of the Γ-module of `R`. -/
noncomputable def gammaShiftHom
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [CategoryTheory.Linear ℂ D]
    [MonoidalLinear ℂ D]
    (L : OddLine D) (R : D) [MonObj R]
    [IsCommMonObj R] :
    gammaModule D L R ((freeMod R L.obj).X) ⟶
      SuperCommAlgebra.Mod.shift (gammaModule D L R R) where
  evenMap := (rhoEvenOdd L R).toLinearMap
  oddMap := (rhoOddOdd L R).toLinearMap
  map_actEE x m := by
    refine free_cap_slide' L R x m (λ_ (𝟙_ D)).inv (λ_ L.obj).inv
      (λ_ L.obj).inv (λ_ L.obj).inv (rhoEvenOdd_eq_cap L R)
      (rhoEvenOdd_eq_cap L R) ?_
    monoidal
  map_actEO x m := by
    refine free_cap_slide' L R x m (λ_ L.obj).inv L.sq.inv
      L.sq.inv (λ_ (𝟙_ D)).inv (rhoOddOdd_eq_cap L R)
      (rhoOddOdd_eq_cap L R) ?_
    have hc : (λ_ L.obj).inv ▷ L.obj ≫
        (α_ (𝟙_ D) L.obj L.obj).hom =
        (λ_ (L.obj ⊗ L.obj)).inv := by monoidal
    rw [hc]
    exact leftUnitor_inv_naturality L.sq.inv
  map_actOE u m := by
    refine free_cap_slide' L R u m (ρ_ L.obj).inv L.sq.inv
      (λ_ L.obj).inv L.sq.inv (rhoOddOdd_eq_cap L R)
      (rhoEvenOdd_eq_cap L R) ?_
    have hc : (ρ_ L.obj).inv ▷ L.obj ≫
        (α_ L.obj (𝟙_ D) L.obj).hom =
        L.obj ◁ (λ_ L.obj).inv := by monoidal
    rw [hc]
  map_actOO u m := by
    refine free_cap_slide' L R u m L.sq.inv (λ_ L.obj).inv
      L.sq.inv (ρ_ L.obj).inv (rhoEvenOdd_eq_cap L R)
      (rhoOddOdd_eq_cap L R) ?_
    have h2 : L.sq.inv ▷ L.obj ≫ (α_ L.obj L.obj L.obj).hom =
        (λ_ L.obj).hom ≫ (ρ_ L.obj).inv ≫
          L.obj ◁ L.sq.inv := by
      rw [← reassoc_of% L.evaluation_coevaluation,
        ← MonoidalCategory.whiskerLeft_comp, Iso.hom_inv_id,
        MonoidalCategory.whiskerLeft_id, Category.comp_id]
    rw [h2, ← Category.assoc, Iso.inv_hom_id, Category.id_comp]

end Shift
end RS
end
