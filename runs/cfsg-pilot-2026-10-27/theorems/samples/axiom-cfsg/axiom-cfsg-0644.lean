public section

namespace CFSG.GH74.GLS.IVK

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher

variable {p f : ℕ} {E : Type} [Field E] {V : Type} [AddCommGroup V] [Module E V]

namespace PairedSL

variable {h : UnitaryFieldData p f E} {B : V →ₛₗ[h.bar] V →ₗ[E] E} {Y : Subgroup (sesqUnitaryGroup B)}
  (P : PairedSL h B Y)

theorem vec_injective : Function.Injective P.vec := by
  intro u u' huu
  have h1 : P.cp.symm u = P.cp.symm u' := Subtype.ext huu
  exact P.cp.symm.injective h1

end PairedSL
end CFSG.GH74.GLS.IVK
end
