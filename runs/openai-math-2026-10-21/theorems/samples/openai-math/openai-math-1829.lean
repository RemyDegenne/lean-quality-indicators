namespace OAI

noncomputable section

namespace HyperbolicObstruction.ConeSkeleton.RelDisk

open IncidenceTemplate CoreGeometry LetterPresentation PictureSwitch Equiv Equiv.Perm

attribute [local instance] Classical.propDecidable

universe u

variable (n : ℕ) (w : TableModel.Entry (A := Alphabet n) rowSupport → Bool)
  (d : (Fin 6 → Alphabet n) → Bool)

variable (ell : ℕ) (hell : 0 < ell) (word : Fin ell → Alphabet n)

variable {A : Type*} [AddCommGroup A]

variable (c : Top n w → MacroGraph.graph.Dart → A)
  (hc : ∀ a e, c a e.symm = -c a e) (f : FrozenCell n w d → A)

variable (P : WalkPicture.{0} (target n w d ell hell word c hc f))

variable (select : P.Face → Bool) (b : Fan n w)

lemma mark_absent (z : ApexInstance n w d ell hell word c hc f P select b) (x : P.Link z.val) :
    fragmentMark n w d ell hell word c hc f P select b z x = .absent ↔ select (P.faceClass x.val) ≠ true := by
  unfold fragmentMark
  split_ifs <;> simp_all

end HyperbolicObstruction.ConeSkeleton.RelDisk
end
end OAI
