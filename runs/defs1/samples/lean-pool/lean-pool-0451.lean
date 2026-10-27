@[expose] public section

namespace FirstOrder.Language

open FirstOrder Structure

variable {L : Language.{0, 0}}

/-- **Totality** of the graph relation of `f`: `∀ xs, ∃ y, G_f(xs, y)` — output variable last. -/
def graphTotality {n : ℕ} (f : L.Functions n) : (graphLanguage L).Sentenceω :=
  .forallBlock (k := n) (.existsBlock (k := 1)
    (.rel (GraphRelation.graph f)
      (Fin.snoc (fun j => Term.var (Sum.inr (Fin.castAdd 1 (Fin.natAdd 0 j))))
        (Term.var (Sum.inr (Fin.natAdd (0 + n) 0))))))

end FirstOrder.Language
end
