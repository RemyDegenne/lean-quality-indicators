namespace OAI

section

namespace Erdos3.NativeSampleCorrelation

open RationalFilteredNilmanifold

open scoped TensorProduct BigOperators

attribute [local instance] NativeMultidegreeNilcharacter.lie NativeMultidegreeNilcharacter.algebra
  NativeMultidegreeNilcharacter.topology NativeMultidegreeNilcharacter.topologicalAdd
  NativeMultidegreeNilcharacter.continuousSMul NativeMultidegreeNilcharacter.hausdorff
  NativeSampleCorrelation.lie NativeSampleCorrelation.algebra
  NativeSampleCorrelation.topology NativeSampleCorrelation.topologicalAdd
  NativeSampleCorrelation.continuousSMul NativeSampleCorrelation.hausdorff

variable {p q : ℝ} {N : ℕ} [NeZero N]
  {W : NativeMultidegreeNilcharacter (fun _ : QuarticReplicatedIndex => 1) p} {i j : Fin (W.tensorPower 6).outputDim}
  (V : NativeSampleCorrelation (fun _ : Fin 4 => 1) 3 q
    Finset.univ (fun z : Fin 4 → ZMod N => fun k => ((z k).val : ℤ))
    (fun z => (W.tensorPower 6).quarticAntisymmetric i j (fun k => ((z k).val : ℤ))))

variable [TopologicalSpace (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [IsTopologicalAddGroup (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [ContinuousSMul ℝ (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]
  [T2Space (ℝ ⊗[ℚ] V.QuarticPairAlgebra)]

theorem quarticPairCoordinateNiltest_orbit (k : Fin 2) (out : Fin W.outputDim) :
    (V.quarticPairCoordinateNiltest k out).orbit = V.quarticPairNiltest.orbit := by
  change NilpotentLieFiltration.piRealOrbit _ _ = NilpotentLieFiltration.piRealOrbit _ _
  apply congrArg (NilpotentLieFiltration.piRealOrbit
    (fun l => (V.quarticPairModels l).filtration))
  funext l
  cases l with
  | none => rfl
  | some l => fin_cases k <;> fin_cases l <;> rfl

end Erdos3.NativeSampleCorrelation
end
end OAI
