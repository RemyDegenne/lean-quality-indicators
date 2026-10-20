@[expose] public section

namespace Lean4GlCoalgebras

infixr:6 "⊢" => proves

prefix:40 "⊢" => Sequent.isTrue

lemma node_in_pg_sequent_in_FL (𝕏 : Proof) (x : 𝕏.X) :
  ∀ y : (pointGeneratedProof 𝕏 x).X, f (r (αPoint 𝕏 x) y) ⊆ Sequent.FL (f (r 𝕏.α x)) := by
  intro y
  exact path_in_FL y.2

end Lean4GlCoalgebras
end
