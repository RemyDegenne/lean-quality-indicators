namespace OAI

noncomputable section

open scoped BigOperators

namespace SparseHoles

open scoped BigOperators

lemma mem_rimEdges (H : Finset Vertex) (e : Edge) :
    e∈rimEdges H ↔ e∈(rimNet H).edgeSet ∧ ∀ z∈e, z∈rim H := by
  classical
  simp only [rimEdges,Finset.mem_filter]
  refine ⟨And.right,fun h => ⟨?_,h⟩⟩
  induction e using Sym2.inductionOn with
  | _ x y =>
    apply (mem_incidentEdges _ _).mpr
    exact ⟨h.1.1,x,(mem_rimFin H x).mpr (h.2 x (by simp)),by simp⟩

end SparseHoles
end
end OAI
