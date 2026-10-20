@[expose] public section

universe u v w

namespace MvPolynomial

theorem idealOfVars_map_rename
    {σ : Type u} {τ : Type v} {R : Type w} [CommSemiring R] (f : σ → τ) :
    (idealOfVars σ R).map (rename (R := R) f).toRingHom =
      Ideal.span ((X : τ → MvPolynomial τ R) '' Set.range f) := by
  rw [idealOfVars, Ideal.map_span, ← Set.range_comp]
  have hX : (rename (R := R) f).toRingHom ∘
      (X : σ → MvPolynomial σ R) = (X : τ → MvPolynomial τ R) ∘ f := by
    funext i
    exact rename_X _ i
  rw [hX, Set.range_comp]

end MvPolynomial
end
