@[expose] public section

open CategoryTheory

universe u v

namespace MulAction

variable {G : Type u} {X : Type v} [Group G] [MulAction G X]

variable [IsPretransitive G X] (x : X)

theorem normalizerQuotientEquivAut_symm_apply_eq_mk_iff
    (a : Aut (Action.ofMulAction G X)) (n : Subgroup.normalizer (stabilizer G x : Set G)) :
    (normalizerQuotientEquivAut (G := G) x).symm a = QuotientGroup.mk n ↔
      a.hom.hom x = (n : G)⁻¹ • x := by
  rw [MulEquiv.symm_apply_eq]
  constructor
  · intro h
    rw [h, normalizerQuotientEquivAut_mk_apply_self]
  · intro h
    apply actionAut_eq_of_value_eq x
    rw [normalizerQuotientEquivAut_mk_apply_self]
    exact h

end MulAction
end
