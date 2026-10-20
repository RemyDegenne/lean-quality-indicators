@[expose] public section

namespace RS

open CategoryTheory MonoidalCategory Limits

open scoped MonObj

universe v u

variable {D : Type u}

attribute [local instance]
  hasBinaryBiproducts_of_finite_biproducts

/-- **Transport of a dévissage state along an isomorphism** of
the object being decomposed. -/
noncomputable def DevissageState.transportObj
    [Category.{v} D] [MonoidalCategory D] [SymmetricCategory D]
    [Preadditive D] [MonoidalPreadditive D] [HasFiniteBiproducts D]
    [HasCoequalizers D]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorLeft Z)]
    [∀ Z : D, PreservesColimitsOfShape WalkingParallelPair (tensorRight Z)]
    {L : OddLine D} {X Y : D} (e : X ≅ Y)
    (st : DevissageState D L X) : DevissageState D L Y :=
  letI := st.monObj
  letI := st.comm
  { base := st.base
    monObj := st.monObj
    comm := st.comm
    unit_ne_zero := st.unit_ne_zero
    units := st.units
    lines := st.lines
    rest := st.rest
    restDual := st.restDual
    datum := st.datum
    zigzag := st.zigzag
    decomp := st.decomp.elim fun f =>
      ⟨(freeModMapIso st.base e.symm).trans f⟩ }

end RS
end
