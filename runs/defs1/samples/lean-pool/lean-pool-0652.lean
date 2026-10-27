@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

/-- **The dual split idempotent** on the base change of the dual
module: evaluate, then coevaluate. -/
noncomputable def splitIdemDual
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [HasCoequalizers D] (A : D) [MonObj A] [IsCommMonObj A] {M : Mod D A}
    {M' : Mod D A} (B : D) [MonObj B] [IsCommMonObj B] (φ : A ⟶ B)
    [IsMonHom φ]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    (v : M.X ⟶ B) (w : M'.X ⟶ B) (d : ModDualityDatum A M M')
    (hv : actLeft A M.X ≫ v =
      (A ◁ v) ≫ (φ ▷ B) ≫ μ[B])
    (hw : actLeft A M'.X ≫ w =
      (A ◁ w) ≫ (φ ▷ B) ≫ μ[B]) :
    baseChange φ M' ⟶ baseChange φ M' :=
  splitEval A B φ w hw ≫ splitCoevalDual A B φ v d hv

end RS
end
