namespace OAI

noncomputable section

open Set

open scoped ENNReal

open Set Filter Topology

open scoped Classical

namespace BoundedTreePotentials.Segments.Atom

lemma opposite_starts {C : Set Node} (hC : Initial C) {g : Node → ℝ}
    (hsupp : ∀ v ∉ C, g v=0) (A B : Atom) {q : Node} (hq : IsExit C q)
    (hop : A.exitCoeff g q*B.exitCoeff g q < 0) :
    (Prefix (A.original q).start (B.original q).start ∨
      Prefix (B.original q).start (A.original q).start) ∧
    (A.original q).start ≠ (B.original q).start := by
  have hnA : A.exitCoeff g q ≠ 0 := by intro he; rw [he,zero_mul] at hop; exact (lt_irrefl _ hop)
  have hnB : B.exitCoeff g q ≠ 0 := by intro he; rw [he,mul_zero] at hop; exact (lt_irrefl _ hop)
  obtain ⟨hAm,hAq⟩ := A.original_spec (A.exitCoeff_ne_zero hnA)
  obtain ⟨hBm,hBq⟩ := B.original_spec (B.exitCoeff_ne_zero hnB)
  refine ⟨prefix_chain (((A.original q).mem_nodes q).mp hAq).1
    (((B.original q).mem_nodes q).mp hBq).1,?_⟩
  intro hstart
  have he : A.exitCoeff g q=B.exitCoeff g q := by
    rw [A.exitCoeff_eq g hAm hAq,B.exitCoeff_eq g hBm hBq,
      Segment.eval_to_exit hC hsupp _ hAq hq.1,Segment.eval_to_exit hC hsupp _ hBq hq.1]
    congr 2
  rw [he] at hop
  nlinarith [sq_nonneg (B.exitCoeff g q)]

end BoundedTreePotentials.Segments.Atom
end
end OAI
