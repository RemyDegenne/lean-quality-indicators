public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.RuType CFSG.QuasithinUnique.Setup.Family CFSG.LieType.SteinbergBR

open scoped MatrixGroups

theorem congr_conj {A B : Type*} [Group A] [Group B] (e : A ≃* B) (a : A) :
    MulAut.congr e (MulAut.conj a) = MulAut.conj (e a) :=
  MulEquiv.ext fun b => by
    show e (a * e.symm b * a⁻¹) = e a * b * (e a)⁻¹
    rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

end CFSG.Quasithin.H13.L32A
end
