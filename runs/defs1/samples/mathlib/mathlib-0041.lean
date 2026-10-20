@[expose] public section

noncomputable section

universe v v₂ u u' u₂

open CategoryTheory

open CategoryTheory.Limits.WalkingParallelPair

namespace CategoryTheory.Limits

variable {C : Type u} [Category.{v} C]

variable [HasZeroMorphisms C]

variable {X Y : C} (f : X ⟶ Y)

section

variable {f}

/-- Any zero object identifies to the cokernel of a given epimorphisms. -/
def CokernelCofork.IsColimit.ofEpiOfIsZero {X Y : C} {f : X ⟶ Y} (c : CokernelCofork f)
    (hf : Epi f) (h : IsZero c.pt) : IsColimit c :=
  isColimitAux _ (fun _ => 0) (fun s => by rw [comp_zero, ← cancel_epi f, comp_zero, s.condition])
    (fun _ _ _ => h.eq_of_src _ _)

end
end CategoryTheory.Limits
end
end
