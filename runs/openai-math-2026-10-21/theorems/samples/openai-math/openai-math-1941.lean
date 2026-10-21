namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm

attribute [local instance] Classical.propDecidable

universe u

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

variable {A : Type*} [AddCommGroup A]

variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

variable (P : WalkPicture.{u} (walkTarget n w d c hc f)) (select : P.Face → Bool)

variable (hm : P.FrozenMapped (walkFrozenTarget n w d c hc f))

lemma frozenFaceDart_injective (k : FrozenCell n w d) : Function.Injective
    (fun p : KindFace n w d c hc f P select (.inr k) × Fin ((frozenBoundary n w d).size k) =>
      frozenFaceDart n w d c hc f P select hm k p.1 p.2) := by
  intro p q h
  apply Prod.ext
  · apply Subtype.ext
    have hf := congrArg P.faceClass h
    simpa only [frozenFaceDart_face] using hf
  · obtain ⟨o,ho⟩ := frozenFaceDart_index n w d c hc f P select hm k p.1 p.2
    obtain ⟨o',ho'⟩ := frozenFaceDart_index n w d c hc f P select hm k q.1 q.2
    have hh := congrArg P.index h
    rw [ho,ho'] at hh
    have he : (o, p.2) = (o', q.2) := eq_of_heq (Sigma.mk.inj_iff.mp (Sum.inr.inj hh)).2
    exact congrArg (fun t : Bool × Fin ((frozenBoundary n w d).size k) => t.2) he

end HyperbolicObstruction.ConeSkeleton
end
end OAI
