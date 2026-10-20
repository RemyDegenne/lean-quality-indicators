public section

open TauCeti.Bialgebra _root_.Bialgebra _root_.Coalgebra WithConv

namespace TauCeti

section Hopf

open TrivSqZeroExt WithConv _root_.Bialgebra Bialgebra.CounitAlgebra

variable {R A B : Type*} [CommSemiring R] [CommSemiring A] [HopfAlgebra R A]
  [CommSemiring B] [Algebra R B]

lemma derivationMulEquivTangentKer_apply_fst
    (d : Multiplicative (Derivation R A (Bialgebra.CounitAlgebra R A B))) (a : A) :
    fst (R := CounitAlgebra R A B)
        ((derivationMulEquivTangentKer R A B d).val.ofConv a) =
      algebraMap A (CounitAlgebra R A B) a := by
  simp only [derivationMulEquivTangentKer, MulEquiv.coe_mk, Equiv.coe_fn_mk,
    WithConv.ofConv_toConv, derivationToDualNumberEquivLift_apply_fst]

end Hopf
end TauCeti
end
