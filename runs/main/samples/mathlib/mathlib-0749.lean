@[expose] public section

open MulOpposite

universe u v

attribute [instance 100] UnitalShelf.toOne

scoped[Quandles] infixr:65 " ◃ " => Shelf.act

scoped[Quandles] infixr:65 " ◃⁻¹ " => Rack.invAct

scoped[Quandles] infixr:25 " →◃ " => ShelfHom

open scoped Quandles

namespace Rack

variable {R : Type*} [Rack R]

export Shelf (self_distrib)

@[simp]
theorem invAct_apply (x y : R) : (act' x)⁻¹ y = x ◃⁻¹ y :=
  rfl

end Rack
end
