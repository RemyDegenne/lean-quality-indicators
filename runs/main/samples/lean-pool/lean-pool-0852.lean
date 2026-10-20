@[expose] public section

namespace QuasiBorelSpace.Pi

variable
  {A : Type*} {_ : QuasiBorelSpace A}
  {B : Type*} {_ : QuasiBorelSpace B}
  {C : Type*} {_ : QuasiBorelSpace C}
  {I : Type*} {P : I → Type*} {_ : ∀ i, QuasiBorelSpace (P i)}

@[simp]
lemma isHom_iff {f : A → (i : I) → P i} : IsHom f ↔ ∀i, IsHom (f · i) := by
  apply Iff.intro
  · fun_prop
  · exact isHom_pi

end QuasiBorelSpace.Pi
end
