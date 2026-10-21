namespace OAI

universe contextUniverse1 contextUniverse2

universe portUniverse1 portUniverse2 portUniverse3 portUniverse4 portUniverse5 portUniverse6 portUniverse7 portUniverse8 portUniverse9 portUniverse10 portUniverse11 portUniverse12 portUniverse13 portUniverse14 portUniverse15 portUniverse16 portUniverse17 portUniverse18 portUniverse19 portUniverse20 portUniverse21 portUniverse22 portUniverse23 portUniverse24 portUniverse25 portUniverse26 portUniverse27 portUniverse28 portUniverse29 portUniverse30 portUniverse31 portUniverse32 portUniverse33 portUniverse34 portUniverse35 portUniverse36 portUniverse37 portUniverse38 portUniverse39 portUniverse40 portUniverse41 portUniverse42 portUniverse43 portUniverse44 portUniverse45 portUniverse46 portUniverse47 portUniverse48 portUniverse49 portUniverse50 portUniverse51 portUniverse52 portUniverse53 portUniverse54 portUniverse55 portUniverse56 portUniverse57 portUniverse58 portUniverse59 portUniverse60 portUniverse61 portUniverse62 portUniverse63 portUniverse64 portUniverse65 portUniverse66 portUniverse67 portUniverse68 portUniverse69 portUniverse70 portUniverse71 portUniverse72 portUniverse73 portUniverse74 portUniverse75 portUniverse76

section

noncomputable section

open scoped Classical

noncomputable section

open scoped Classical BigOperators

open Equiv Equiv.Perm

namespace OddKaplansky.Planar

open Equiv Equiv.Perm

variable {α : Type portUniverse36} {V : Type portUniverse37} {F : Type portUniverse38} {A : Type portUniverse39} {B : Type portUniverse40} [Fintype α] [CommGroup A] [Group B]

variable {R : Ribbon α} {Inc : V → F → Prop} {ι : V → F → (A →* B)}

lemma NoncommBalanced.boundary_reduced (D : NoncommBalanced R Inc ι) (hred : D.Reduced)
    (hshort : ShortWords Inc ι) {a : α}
    (ha : cycleClass R.face a ≠ D.exceptionFace) (n : ℕ) :
    _root_.OAI.SimpleGraph.Walk.Reduced (D.boundary a n) := by
  apply SimpleGraph.Walk.reduced_of_getVert
  intro i hi
  rw [D.boundary_length] at hi
  have he : i = 2 * (i / 2) ∨ i = 2 * (i / 2) + 1 := by omega
  rcases he with he | he
  · rw [he, D.boundary_getVert_even n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 2 = 2 * (i / 2 + 1) := by omega
    rw [hk, D.boundary_getVert_even n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inr.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.whiteLabel ((R.face ^ (i / 2)) a) =
      D.whiteLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    rw [D.whiteLabel_rot] at hh
    exact hred.2.1 _ (D.black_not_fixed_on_other_face hred hshort (by rwa [cycleClass_pow])) hh.symm
  · rw [he, D.boundary_getVert_odd n (i / 2) (by omega)]
    have hk : 2 * (i / 2) + 1 + 2 = 2 * (i / 2 + 1) + 1 := by omega
    rw [hk, D.boundary_getVert_odd n (i / 2 + 1) (by omega)]
    intro h
    have hh := Sum.inl.inj h
    rw [pow_succ', Perm.mul_apply] at hh
    change D.blackLabel ((R.face ^ (i / 2)) a) =
      D.blackLabel (R.white (R.black ((R.face ^ (i / 2)) a))) at hh
    have hn : R.white (R.black ((R.face ^ (i / 2)) a)) ≠
        R.black ((R.face ^ (i / 2)) a) :=
      D.white_not_fixed hred.1 _
    exact hred.2.2 _ hn (hh.symm.trans (D.blackLabel_rot _).symm)

end OddKaplansky.Planar
end
end
end
end OAI
