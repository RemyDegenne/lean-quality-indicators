@[expose] public section

universe uR uS uM

open scoped Pointwise

namespace ModuleCat.RightExtension

variable {R : Type uR} [Ring R]

section IdealQuotient

variable {M : Type uM} [AddCommGroup M] [Module Rᵐᵒᵖ M]

/-- The map induced by `m ↦ m ⊗ 1` from the quotient module to extension of
scalars. -/
def fromIdealQuotient (I : Ideal R) [I.IsTwoSided] :
    IdealQuotient (M := M) I →ₗ[(R ⧸ I)ᵐᵒᵖ] Obj (Ideal.Quotient.mk I) M where
  toFun := fromIdealQuotientSemilinear (M := M) I
  map_add' := (fromIdealQuotientSemilinear (M := M) I).map_add
  map_smul' s x := by
    induction s using MulOpposite.rec' with
    | _ s =>
        obtain ⟨r, rfl⟩ := Ideal.Quotient.mk_surjective s
        induction x using Submodule.Quotient.induction_on with
        | _ m =>
            change fromIdealQuotientSemilinear (M := M) I
                ((MulOpposite.op (Ideal.Quotient.mk I r)) •
                  Submodule.Quotient.mk
                    (p := idealSubmodule (M := M) I) m) = _
            change fromIdealQuotientSemilinear (M := M) I
                (Submodule.Quotient.mk
                  (p := idealSubmodule (M := M) I)
                  (MulOpposite.op r • m)) = _
            rw [fromIdealQuotientSemilinear_mk,
              fromIdealQuotientSemilinear_mk]
            exact (tmulOne (Ideal.Quotient.mk I)).map_smulₛₗ
              (MulOpposite.op r) m

end IdealQuotient
end ModuleCat.RightExtension
end
