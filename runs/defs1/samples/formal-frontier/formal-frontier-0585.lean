@[expose] public section

namespace Polynomial

universe u

variable {R : Type u} [CommRing R]

/-- Evaluation at zero on the quotient by `C r * X`. -/
noncomputable def quotientSpanCMulXEval (r : R) :
    (R[X] ⧸ Ideal.span ({C r * X} : Set R[X])) →ₐ[R] R :=
  Ideal.Quotient.liftₐ _ (aeval (0 : R)) (by
    intro p hp
    have hle : Ideal.span ({C r * X} : Set R[X]) ≤
        RingHom.ker (aeval (0 : R)).toRingHom :=
      Ideal.span_le.mpr (by
        intro q hq
        have hq' : q = C r * X := by simpa only [Set.mem_singleton_iff] using hq
        subst q
        simp [RingHom.mem_ker])
    exact RingHom.mem_ker.mp (hle hp))

end Polynomial
end
