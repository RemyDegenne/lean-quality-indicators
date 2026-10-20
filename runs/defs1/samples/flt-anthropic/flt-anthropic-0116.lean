namespace P2MW.S_CuspForm_petersson_heckeTLin

set_option autoImplicit false

noncomputable section

open MeasureTheory UpperHalfPlane ModularForm Filter

open scoped MatrixGroups ModularForm ComplexConjugate Modular ENNReal Pointwise

namespace AlliAux1R6

section conjugation

variable {N p : ℕ} (Z : Bez N p)

namespace Bez

def Ymat (h : CongruenceSubgroup.Gamma0 (N * p)) : Matrix (Fin 2) (Fin 2) ℤ :=
  !![((p : ℤ) * ea h - Z.v * ec h) * Z.u + (p * eb h - Z.v * ed h) * N,
      ea h * Z.v - Z.v ^ 2 * N * et h + p * eb h - Z.v * ed h;
    (p : ℤ) * (-(N * ea h * Z.u) + Z.u ^ 2 * ec h - N * N * eb h + N * Z.u * ed h),
      (-(N * ea h) + Z.u * ec h) * Z.v + (-(N * eb h) + Z.u * ed h) * p]

end Bez
end conjugation
end AlliAux1R6
end
end P2MW.S_CuspForm_petersson_heckeTLin
