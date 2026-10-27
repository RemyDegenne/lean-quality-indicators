public section

namespace TauCeti

universe u v w x₁ x₂ x₃

variable {ι : Type u} {X : Type v} {Y : Type w} [AddCommGroup X] [AddCommGroup Y]
  (P : RootDatum ι X Y) (b : P.Base)

namespace NormalCrystal

variable {P b} {B : Type x₁} {B' : Type x₂} {B'' : Type x₃}

namespace StrictHom

variable {c : NormalCrystal P b B} {d : NormalCrystal P b B'} {d' : NormalCrystal P b B''}

variable (ψ : StrictHom c d) (i : b.support) (x : B)

/-- A strict morphism is also a strict morphism between the dual crystals. -/
def dual : StrictHom c.dual d.dual where
  toFun := ψ
  wt_toFun x := by simp
  e_toFun i x := by simp

end StrictHom
end NormalCrystal
end TauCeti
end
