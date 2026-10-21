namespace OAI

namespace Erdos970

open scoped _root_.Erdos970

section

open _root_.Set _root_.MeasureTheory

namespace ErdosOmissionTail

open ErdosContinuousOmission ErdosContinuousBoundary ErdosOmissionBindings

open NumberTheoryLean.FinitePathGeometry

theorem terminalBlock_mask (S y : ℝ) {b : ℝ} (_hb1 : 1 ≤ b) (hb2 : b ≤ 2) :
    terminalBlock (2*y+2-S) b=
      ∫ a in Icc (1:ℝ) b,if S/2+a ≤ y then
        gate omissionForce .even (2*y+2-S-a) a/(max 1 a) else 0 := by
  have hset : Ioc (1:ℝ) (upperCutoff .odd (2*y+2-S) b)=
      Ioc (1:ℝ) b ∩ {a : ℝ | S/2+a ≤ y} := by
    ext a
    constructor
    · intro ha
      obtain ⟨ha1,ha2,hab,hgate⟩ := (mem_upperCutoff .odd (2*y+2-S) b a).mp ha
      have hh := (strong_gate_below_two ha2).mp hgate
      exact ⟨⟨ha1,hab⟩,by change S/2+a ≤ y; linarith⟩
    · rintro ⟨⟨ha1,hab⟩,hy⟩
      apply (mem_upperCutoff .odd (2*y+2-S) b a).mpr
      refine ⟨ha1,hab.trans hb2,hab,?_⟩
      apply (strong_gate_below_two (hab.trans hb2)).mpr
      change S/2+a ≤ y at hy
      linarith
  have hm : MeasurableSet {a : ℝ | S/2+a ≤ y} :=
    measurableSet_le (measurable_const.add measurable_id) measurable_const
  change (∫ a : ℝ in 1..upperCutoff .odd (2*y+2-S) b,
    gate omissionForce .even (2*y+2-S-a) a/(max 1 a))=_
  rw [intervalIntegral.integral_of_le (upperCutoff_bounds .odd (2*y+2-S) b).1,
    hset,← setIntegral_indicator hm,← integral_Icc_eq_integral_Ioc]
  rfl

end ErdosOmissionTail
end
end Erdos970
end OAI
