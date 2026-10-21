namespace OAI

noncomputable section

open scoped BigOperators lp

open Complex Matrix

namespace AtomicTriangular.Construction

lemma rowNode_cover (n : Node) (hn : n.val∈FiniteNodes) (d : Fin 2) :
    ∃ i : Fin 20,rowNode i=n ∧ rowDerivative i=d := by
  obtain ⟨j,hj⟩ := finiteNode_surj hn
  refine ⟨⟨2*j.val+d.val,by omega⟩,?_,?_⟩
  · apply Subtype.ext
    change finiteNode ⟨(2*j.val+d.val)/2,by omega⟩=n.val
    convert hj using 1
    congr 1
    apply Fin.ext
    dsimp
    omega
  · apply Fin.ext
    change (2*j.val+d.val)%2=d.val
    omega

end AtomicTriangular.Construction
end
end OAI
