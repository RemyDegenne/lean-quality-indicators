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

@[reassoc]
lemma cyclesCokernelIso_inv_naturality {B : D}
    (R' : AcyclicResolution X B) (f : R.cocomplex ⟶ R'.cocomplex) (n : ℕ)
    [Subsingleton (Ext X (R.cyclesShortComplex n).X₂ 1)]
    [Subsingleton (Ext X (R'.cyclesShortComplex n).X₂ 1)] :
    AddCommGrpCat.ofHom ((mk₀ (HomologicalComplex.cyclesMap f n)).postcomp X
        (add_zero 1)) ≫
        (R'.cyclesCokernelIso n).inv =
      (R.cyclesCokernelIso n).inv ≫ R.extZeroCokernelMap R' f n := by
  rw [← cancel_epi (R.cyclesCokernelIso n).hom,
    Iso.hom_inv_id_assoc,
    ← R.cyclesCokernelIso_hom_naturality_assoc R' f n,
    Iso.hom_inv_id, Category.comp_id]

end AcyclicResolution
end SameUniverse
end CategoryTheory.Abelian.Ext
end
end
