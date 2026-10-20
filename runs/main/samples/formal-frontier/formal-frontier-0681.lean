@[expose] public section

universe uι uR uS uM uN

namespace KTheory

namespace ProjectiveClass

section Prod

variable (R : Type uR) (S : Type uS) [Ring R] [Ring S]

theorem prod_map_prodEquiv_symm (a : ProjectiveClass R × ProjectiveClass S) :
    (map (RingHom.fst R S) ((prodEquiv R S).symm a),
      map (RingHom.snd R S) ((prodEquiv R S).symm a)) = a := by
  change prodEquiv R S ((prodEquiv R S).symm a) = a
  exact (prodEquiv R S).apply_symm_apply a

end Prod
end ProjectiveClass
end KTheory
end
