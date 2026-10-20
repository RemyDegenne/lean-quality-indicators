public section

namespace TauCeti.DynkinType

open _root_.LieAlgebra _root_.LieAlgebra.IsKilling LieModule

noncomputable section

theorem f4RootCartanWeight_simple (α : Fin 48) (i : Fin F4.rank) :
    rootCartanWeight (f4KillingRoot α)
        (((F4.lieBasis valid_F4).baseSupportEquiv i :
          (F4.cartanSubalgebra valid_F4).root) :
            Weight ℚ (F4.cartanSubalgebra valid_F4) (F4.lieAlgebra valid_F4)) =
      f4SimplyConnectedRootDatum.pairing α
        (Fin.castAdd 44 (Fin.cast rank_F4 i)) := by
  apply (Int.cast_injective : Function.Injective (fun z : ℤ => (z : ℚ)))
  rw [intCast_rootCartanWeight_apply]
  rw [← rootSystem_pairing_apply (F4.cartanSubalgebra valid_F4)
    ((F4.lieBasis valid_F4).baseSupportEquiv i) (f4KillingRootLabel α)]
  rw [← F4.rationalRootSystemEquiv_indexEquiv_simpleIndex valid_F4 i,
    (F4.rationalRootSystemEquiv valid_F4).toHom.pairing,
    F4.pairing_rationalRootSystem, simplyConnectedRootDatum_F4]
  norm_cast
  have hs : F4.simpleIndex valid_F4 i =
      Fin.castAdd 44 (Fin.cast rank_F4 i) := by
    -- These casts identify the rank-four node type without changing its underlying numeral.
    have hi : i = Fin.cast rank_F4 i := by
      apply Fin.ext
      rfl
    rw [hi]
    exact simpleIndex_F4 valid_F4 (Fin.cast rank_F4 i)
  rw [hs]
  congr 1

end
end TauCeti.DynkinType
end
