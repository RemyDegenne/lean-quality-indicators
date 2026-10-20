@[expose] public section

universe u v w

open CategoryTheory CategoryTheory.IsCofiltered Set CategoryTheory.FunctorToTypes

namespace CategoryTheory

namespace Functor

variable {J : Type u} [Category* J] (F : J ⥤ Type v) {i j k : J} (s : Set (F.obj i))

variable [IsCofilteredOrEmpty J]

section FiniteCofilteredSystem

variable [∀ j : J, Nonempty (F.obj j)] [∀ j : J, Finite (F.obj j)]
  (Fsur : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f))

include Fsur

set_option backward.isDefEq.respectTransparency.types false in
set_option backward.defeqAttrib.useBackward true in
theorem eval_section_surjective_of_surjective (i : J) :
    (fun s : F.sections => s.val i).Surjective := fun x => by
  let s : Set (F.obj i) := {x}
  have := F.toPreimages_nonempty_of_surjective s Fsur (singleton_nonempty x)
  obtain ⟨sec, h⟩ := nonempty_sections_of_finite_cofiltered_system (F.toPreimages s)
  refine ⟨⟨fun j => (sec j).val, fun jk => by simpa [Subtype.ext_iff] using! h jk⟩, ?_⟩
  have := (sec i).prop
  simp only [mem_iInter, mem_preimage] at this
  have := this (𝟙 i)
  rwa [map_id, id_apply] at this

end FiniteCofilteredSystem
end Functor
end CategoryTheory
end
