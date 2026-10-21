namespace OAI

section

section

noncomputable section

namespace HyperbolicObstruction.PictureSwitch

open Equiv Equiv.Perm

attribute [local instance] Classical.propDecidable

variable {D : Type*} [DecidableEq D] [Fintype D]

namespace PictureMap

variable (M : PictureMap D) {a b : D} (hab : a ≠ b) (hnext : M.face a = b)

variable {L V : Type*} {label : D → L} {start : L → V} {rev : L → L}

omit [Fintype D] in
lemma boundaryFold_other_face (x : {x // OffPair a b x})
    (hx : ¬ M.face.SameCycle a x.val) :
    ((M.boundaryFold hab hnext).face x).val = M.face x.val := by
  change M.face (swap b (M.face⁻¹ a) x.val) = M.face x.val
  apply congrArg M.face
  apply swap_apply_of_ne_of_ne x.property.2
  intro he
  apply hx
  rw [he]
  have hr : M.face.SameCycle (M.face⁻¹ a) a := by
    simpa only [Perm.inv_def,Equiv.apply_symm_apply] using
      (SameCycle.rfl (f := M.face) (x := M.face⁻¹ a)).apply_right
  exact hr.symm

end PictureMap
end HyperbolicObstruction.PictureSwitch
end
end
end
end OAI
