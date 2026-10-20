public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Abelian.Ext

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

attribute [instance] AcyclicResolution.hasHomology AcyclicResolution.quasiIso

section SameUniverse

variable {D : Type u} [Category.{v} D] [Abelian D] [HasExt.{v} D]

namespace AcyclicResolution

variable {X A : D} (R : AcyclicResolution X A)

/-- The map of dimension-shift cokernels induced by a map of resolution
complexes. -/
@[expose] noncomputable def extZeroCokernelMap {B : D} (R' : AcyclicResolution X B)
    (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ) :
    cokernel ((extFunctorObj X 0).map
      (R.cocomplex.toCycles n (n + 1))) ⟶
        cokernel ((extFunctorObj X 0).map
          (R'.cocomplex.toCycles n (n + 1))) :=
  cokernel.map _ _ ((extFunctorObj X 0).map (f.f n))
    ((extFunctorObj X 0).map (HomologicalComplex.cyclesMap f (n + 1))) (by
      rw [← Functor.map_comp, ← Functor.map_comp,
        toCycles_naturality f n])

end AcyclicResolution
end SameUniverse
end CategoryTheory.Abelian.Ext
end
end
