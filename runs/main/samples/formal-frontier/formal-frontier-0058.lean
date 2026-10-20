@[expose] public section

set_option warningAsError true

universe uR uJ uM uN

namespace AdicCompletion

variable {R : Type uR} [CommRing R] (I : Ideal R)
  {J : Type uJ} (M : J → Type uM)
  [∀ j, AddCommGroup (M j)] [∀ j, Module R (M j)]

@[simp]
theorem piEquivOfFG_apply_apply (hI : I.FG)
    (x : AdicCompletion I (∀ j, M j)) (j : J) :
    piEquivOfFG I M hI x j = map I (LinearMap.proj j) x :=
  congrFun (piEquivOfFG_apply I M hI x) j

end AdicCompletion
end
