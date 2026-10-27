public section

namespace CFSG.Quasithin.MulAutTwo

open Module CFSG.GroupTheory.GLnTwoSplitting

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

variable {V : Type} [CommGroup V]

theorem axisForm_eq_zero [Module (ZMod 2) (Additive V)] (A : Subgroup V) (hA : A.index = 2)
    (w : Additive V) : axisForm A hA w = 0 ↔ Additive.toMul w ∈ A := by
  classical
  show (if Additive.toMul w ∈ A then 0 else 1 : ZMod 2) = 0 ↔ _
  split_ifs with h
  · exact ⟨fun _ => h, fun _ => rfl⟩
  · exact ⟨fun h0 => absurd h0 one_ne_zero, fun h0 => absurd h0 h⟩

end CFSG.Quasithin.MulAutTwo
end
