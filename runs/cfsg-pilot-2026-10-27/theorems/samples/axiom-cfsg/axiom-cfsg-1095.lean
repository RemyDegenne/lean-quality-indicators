public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise

open CFSG.LieType.Universal Matrix

namespace CaseB

variable {G : Type} [Group G] {R : Set (Subgroup G)} {F : Type} [Field F]
  {Ψ : SpecialLinearGroup (Fin 4) F →* G}

section Relations

variable [CharP F 2] [Finite F] (h : Hyp G R) (hS : Skel R Ψ) (hP : PtHyp R Ψ)
  {ι : (Fin 1 → F) → G} (hι : LinParamU R Ψ 1 ι)

include h hS hP hι

omit h hS hP hι in
theorem pi13_conj_xN' (t : F) : pi13 Ψ * xN' R Ψ ι t * (pi13 Ψ)⁻¹ = xU' R Ψ ι t := by
  rw [xN', pi13_inv]
  calc pi13 Ψ * (pi13 Ψ * xU' R Ψ ι t * pi13 Ψ) * pi13 Ψ =
      (pi13 Ψ * pi13 Ψ) * xU' R Ψ ι t * (pi13 Ψ * pi13 Ψ) := by group
    _ = xU' R Ψ ι t := by rw [pm13_mul_self]; group

end Relations
end CaseB
end CFSG.Timmesfeld.ARS
end
