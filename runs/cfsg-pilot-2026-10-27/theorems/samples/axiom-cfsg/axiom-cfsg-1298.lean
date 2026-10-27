public section

set_option autoImplicit true

set_option maxSynthPendingDepth 3

open CFSG

universe u v

variable {k : Type u} [Field k] {G : Type v} [Group G]

open Fintype CategoryTheory CategoryTheory.Limits

namespace CFSG.ClassFun

lemma characterPairingLeft_surjective
    [Fintype G] [CharZero k] :
    Function.Surjective
      (characterPairingLeft (k := k) (G := G)) := by
  have hinj :
    Function.Injective
      (characterPairingLeft (k := k) (G := G)) :=
    characterPairingLeft_injective (k := k) (G := G)

  exact
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank
      (f := characterPairingLeft (k := k) (G := G))
      Subspace.dual_finrank_eq.symm).mp hinj

end CFSG.ClassFun
end
