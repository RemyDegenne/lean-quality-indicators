public section

noncomputable section

universe u

namespace TauCeti.MatrixFactorization

open CategoryTheory Limits

variable {S : Type u} [CommRing S] {w : S}

/-- Take the cokernel of the even-to-odd differential. Its finite generation follows from
that of the odd component, without any condition on the potential. -/
def cokernelFunctor : MatrixFactorization S w ⥤ FGModuleCat.{u} S := by
  let G : MatrixFactorization S w ⥤ Arrow (ModuleCat.{u} S) :=
    { obj X := Arrow.mk X.obj.d₀.hom
      map g := Arrow.homMk g.hom.f₀.hom g.hom.f₁.hom
        (congrArg (fun k => k.hom) g.hom.comm₀)
      map_id X := by ext <;> simp
      map_comp g h := by ext <;> simp }
  exact (ModuleCat.isFG S).lift (G ⋙ coker (ModuleCat.{u} S)) finite_cokernel

end TauCeti.MatrixFactorization
end
end
