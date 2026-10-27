@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **The odd twist of a dévissage state**: the counts change
places and the remainder gains a line factor. -/
noncomputable def twistState
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    (L : OddLine D)
    {X : D}
    (st : DevissageState D L X) :
    DevissageState D L (L.obj ⊗ X) :=
  letI := st.monObj
  letI := st.comm
  { base := st.base
    monObj := st.monObj
    comm := st.comm
    unit_ne_zero := st.unit_ne_zero
    units := st.lines
    lines := st.units
    rest := tensorLeftMod st.base L.obj st.rest
    restDual := tensorLeftMod st.base L.obj st.restDual
    datum := twistDatum st.base L st.datum
    zigzag := twistDatum_zigzag st.base L st.datum st.zigzag
    decomp := st.decomp.elim fun e =>
      ⟨(freeTwistIso st.base L.obj X).trans
        ((tensorLeftModWhiskerIso st.base L.obj e).trans
          ((tensorLeftBiprodIso st.base L.obj
            (freeMod st.base (L.mix st.units st.lines))
            st.rest).trans
            (modBiprodMapIso st.base _ _
              (freeMixTwistIso L st.base st.units st.lines)
              (Iso.refl _))))⟩ }

end RS
end
