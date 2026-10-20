public section

namespace TauCeti

open CategoryTheory

open _root_.TauCeti.Quiver

universe u v w x

variable {k : Type u} {Q : Type v} [Field k] [Quiver.{w} Q]

section ReflectRep

variable [Fintype Q] [∀ a b : Q, Fintype (a ⟶ b)]

variable (M : QuiverRep.{u, v, w, max v w x} k Q) {i : Q} (hi : IsSink i)

@[simp]
theorem reflectRep_map_reflectArrow {b : Q} (e : b ⟶ i) :
    (reflectRep M hi).map (reflectArrow i e).toPath
      = eqToHom (reflectRep_obj_self M hi) ≫
        ModuleCat.ofHom ((LinearMap.proj (⟨b, e⟩ : Σ b : Q, (b ⟶ i))).comp
          (LinearMap.ker (incomingSum M i)).subtype) ≫
        eqToHom (reflectRep_obj_of_ne M hi (hi.ne_of_hom e)).symm := by
  classical
  refine ((reflectRep_map_toPath M hi (reflectArrow i e)).trans
    (dite_eq_right (hi.ne_of_hom e))).trans ?_
  refine (dite_eq_left rfl).trans ?_
  conv_lhs => rw [cast_reflectArrow]
  rfl

end ReflectRep
end TauCeti
end
