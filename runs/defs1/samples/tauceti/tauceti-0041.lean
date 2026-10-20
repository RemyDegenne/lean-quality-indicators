public section

namespace TauCeti

open CategoryTheory CategoryTheory.Abelian LaurentPolynomial

universe w v u t

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  (k : Type t) (e : C ≌ C)

/-- The comparison `(Y{j-1}){1} ≅ Y{j}`, which moves a source shift into the internal degree. -/
noncomputable def shiftSourceObjIso (Y : C) (j : ℤ) :
    e.functor.obj ((e ^ (j - 1)).functor.obj Y) ≅ (e ^ j).functor.obj Y :=
  ((e.powSuccRightIso (j - 1)).app Y).symm ≪≫
    eqToIso (congrArg (fun i : ℤ => (e ^ i).functor.obj Y) (by ring : j - 1 + 1 = j))

end TauCeti
end
