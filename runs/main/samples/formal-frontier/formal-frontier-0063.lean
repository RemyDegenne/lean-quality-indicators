@[expose] public section

universe u v

namespace Algebra.GrothendieckAddGroup

theorem one_mulAddHom {A : Type u} [NonAssocSemiring A] (x : GrothendieckAddGroup A) :
    mulAddHom (of 1) x = x := by
  have h : mulAddHom (of (M := A) 1) = AddMonoidHom.id (GrothendieckAddGroup A) := by
    apply hom_ext
    intro a
    simp only [mulAddHom_of, one_mul, AddMonoidHom.id_apply]
  exact DFunLike.congr_fun h x

end Algebra.GrothendieckAddGroup
end
