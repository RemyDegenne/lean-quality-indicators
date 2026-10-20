@[expose] public section

noncomputable section

namespace EulerPacketCylinderField

open Set MeasureTheory Finset EulerSmoothLimit EulerPacketPointJets EulerPacketProfileRecursion

variable {P T : ℝ} [Fact (0 < P)] {O : Operators} {p : ℕ} {a : ℕ → Profile}

/-- High term field as an element of `Field P T (k.highRaw O p a i j)`. -/
def PrefixFields.highTermField (F : PrefixFields P T p a) (C : CoefficientData P T O)
    (hp : 1 ≤ p) (hT : 0 < T) {correctorT : VectorField}
    (Ct : Field P T correctorT)
    (hCt : TimeDerivative hT.le (F.corrector (p - 1) (Nat.sub_one_lt_of_lt hp)) Ct)
    (pressure : Field P T (pressureGradient (a (p - 1)).highPressure))
    (k : KnownTerm) (i j : ℕ) : Field P T (k.highRaw O p a i j) := by
  by_cases hm : k.meanOnly = true
  · exact (Field.zero P T).congr (fun _ _ _ => by simp [KnownTerm.highRaw, hm])
  · by_cases hz : k.zeroMean = true
    · exact (F.termField C hp hT Ct hCt pressure k i j).congr
        (fun _ _ _ => by simp [KnownTerm.highRaw, hm, hz])
    · exact (F.termField C hp hT Ct hCt pressure k i j).highPart.congr
        (fun _ _ _ => by simp [KnownTerm.highRaw, hm, hz, C.period_eq])

end EulerPacketCylinderField
end
end
