namespace OAI

noncomputable section

namespace HyperbolicObstruction

namespace ConeSkeleton

open IncidenceTemplate CoreGeometry LetterPresentation

attribute [local instance] Classical.propDecidable

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

variable {H : Type*} [_root_.Group H] (c : Dart n w → H)
  (hc : ∀ e, c (rev n w e) = (c e)⁻¹)
  (hcell : ∀ a : Cell n w d, (List.ofFn (fun i => c (side n w d a i))).prod = 1)

include hc hcell in
lemma fanTriangle_relation (f : FanTriangle n w) :
    radialValue n w c f.1 (fanLeft n w f) * c (letterDart n w (fanLetter n w f)) =
      radialValue n w c f.1 (fanRight n w f) := by
  have he := hcell (.inl f)
  change c (.inr ⟨f.1,fanLeft n w f⟩,true) *
    (c (letterDart n w (fanLetter n w f)) *
      (c (.inr ⟨f.1,fanRight n w f⟩,false) * 1)) = 1 at he
  have hr := hc (.inr ⟨f.1,fanRight n w f⟩,true)
  change c (.inr ⟨f.1,fanRight n w f⟩,false) = _ at hr
  rw [hr,mul_one,← mul_assoc] at he
  exact mul_inv_eq_one.mp he

end ConeSkeleton
end HyperbolicObstruction
end
end OAI
