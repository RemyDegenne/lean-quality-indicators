@[expose] public section

noncomputable section

namespace NavierStokes.ParticularWaveBounds

open Set Function Filter

open scoped ContDiff Topology InnerProductSpace BigOperators

open PrimaryPulseBounds

section ComplexSources

open CommonCoverSolve TorusInverse HarmonicCalculus WeightedClasses

/-- Real part, constructed using `LinearMap.toContinuousLinearMap`. -/
noncomputable def realPart : ComplexVector →L[ℝ] ProblemStatement.Space :=
  LinearMap.toContinuousLinearMap {
    toFun := fun a => !₂[(a 0).re, (a 1).re, (a 2).re]
    map_add' := by intro a b; ext i; fin_cases i <;> simp only [Fin.isValue, Pi.add_apply,
        Complex.add_re, Fin.zero_eta, Matrix.cons_val_zero, PiLp.add_apply, Fin.mk_one,
        Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val]
    map_smul' := by intro c a; ext i; fin_cases i <;> simp only [Fin.isValue, Pi.smul_apply,
        Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
        Fin.zero_eta, Matrix.cons_val_zero, RingHom.id_apply, PiLp.smul_apply, smul_eq_mul,
        Fin.mk_one, Matrix.cons_val_one, Fin.reduceFinMk, Matrix.cons_val] }

end ComplexSources
end NavierStokes.ParticularWaveBounds
end
end
