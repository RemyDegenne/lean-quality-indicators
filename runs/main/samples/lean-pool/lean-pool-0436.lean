@[expose] public section

namespace Distributed2Coloring.LowerBound

open scoped BigOperators

namespace Correlation

@[simp] lemma edge_smul_apply {n : Nat} (σ : G n) (e : Edge n) (i : Fin 4) :
    (σ • e).1 i = σ (e.1 i) := rfl

end Correlation
end Distributed2Coloring.LowerBound
end
