public section

namespace CFSG.Quasithin.Stroth

open CFSG.Quasithin CFSG.GH74.BNPair CFSG.GH74.GLS.SP CFSG.Geometry.GeneralizedPolygons

open scoped Pointwise

variable {V : Type} [Fintype V] {Γ : SimpleGraph V} [DecidableRel Γ.Adj]
  {n : ℕ} {D : Type} [Group D] [MulAction D V] [FaithfulSMul D V] [GraphAction D Γ]

theorem pow_reflOneN_mul_reflTwoN_smul_aptEdge {t : ZMod (2 * n) → V}
    (ht : IsPolygonApartment Γ n t) (hn : 3 ≤ n) (hP : IsGeneralizedPolygon Γ n)
    (hT : IsThick Γ) (hM : MoufangCondition D Γ n) (j : ℕ) (k : ZMod (2 * n)) :
    ((((reflOneN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM *
      reflTwoN (D := D) (Γ := Γ) (n := n) t ht hn hP hT hM) ^ j :
      ↥(moufangN D Γ n t)) : D)) • aptEdge t k =
      aptEdge t (k + 2 * (j : ZMod (2 * n))) := by
  induction j generalizing k with
  | zero => simp
  | succ j ih =>
    rw [pow_succ, Subgroup.coe_mul, Subgroup.coe_mul, mul_smul,
      reflOneN_mul_reflTwoN_smul_aptEdge (t := t) ht hn hP hT hM, ih]
    congr 1
    push_cast
    ring

end CFSG.Quasithin.Stroth
end
