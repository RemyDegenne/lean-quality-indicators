namespace OAI

open _root_.MeasureTheory _root_.OAI.MeasureTheory ProbabilityTheory Classical Filter Topology Function

open scoped ENNReal BigOperators Matrix

open Classical

namespace PlanarBoundary

theorem balanced (X : Finset Point) (v : Point) :
    Fintype.card {e : Boundary X // head e = v} =
      Fintype.card {e : Boundary X // tail e = v} := by
  apply (Fintype.card_congr (atVertex X v headOffset)).trans
  apply Eq.trans _ (Fintype.card_congr (atVertex X v tailOffset)).symm
  simp only [Fintype.card_subtype,Finset.card_filter]
  simp only [Fin.sum_univ_succ,headOffset,tailOffset,outward,Matrix.cons_val_zero,
    Matrix.cons_val_succ]
  have ha : v-(1,0)+(0,-1) = v-(1,1) := by ext <;> simp [sub_eq_add_neg,add_assoc]
  have hb : v-(1,1)+(1,0) = v-(0,1) := by ext <;> simp
  have hc : v-(0,1)+(0,1) = v := sub_add_cancel _ _
  have hd : v+(-1,0) = v-(1,0) := by ext <;> simp [sub_eq_add_neg]
  have he : v+(0,-1) = v-(0,1) := by ext <;> simp [sub_eq_add_neg]
  have hf : v-(1,0)+(1,0) = v := sub_add_cancel _ _
  have hg : v-(1,1)+(0,1) = v-(1,0) := by ext <;> simp
  have hh : v-(0,1)+(-1,0) = v-(1,1) := by ext <;> simp [sub_eq_add_neg,add_assoc]
  simp only [show ((0,0) : Point) = 0 from rfl,sub_zero,ha,hb,hc,hd,he,hf,hg,hh]
  by_cases h0 : v ∈ X <;> by_cases h1 : v-(1,0) ∈ X <;>
    by_cases h2 : v-(1,1) ∈ X <;> by_cases h3 : v-(0,1) ∈ X <;> simp [h0,h1,h2,h3]

end PlanarBoundary
end OAI
