@[expose] public section

universe v u

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits HomologicalComplex

variable {ι : Type*}

variable {V : Type u} [Category.{v} V] [Preadditive V]

variable {W : Type*} [Category* W] [Preadditive W]

variable {W₁ W₂ W₃ : Type*} [Category* W₁] [Category* W₂] [Category* W₃]
  [HasZeroMorphisms W₁] [HasZeroMorphisms W₂] [HasZeroMorphisms W₃]

variable {c : ComplexShape ι} {C D : HomologicalComplex V c}

variable (f : C ⟶ D) (i : ι)

namespace CategoryTheory

/-- An additive functor induces a functor between homological complexes.
This is sometimes called the "prolongation".
-/
@[simps, implicit_reducible]
def Functor.mapHomologicalComplex (F : W₁ ⥤ W₂) [F.PreservesZeroMorphisms] (c : ComplexShape ι) :
    HomologicalComplex W₁ c ⥤ HomologicalComplex W₂ c where
  obj C :=
    { X i := F.obj (C.X i)
      d i j := F.map (C.d i j)
      shape i j w := by
        rw [C.shape _ _ w, F.map_zero]
      d_comp_d' := fun i j k _ _ => by rw [← F.map_comp, C.d_comp_d, F.map_zero] }
  map f :=
    { f i := F.map (f.f i)
      comm' := fun i j _ => by
        dsimp
        rw [← F.map_comp, ← F.map_comp, f.comm] }

end CategoryTheory
end
