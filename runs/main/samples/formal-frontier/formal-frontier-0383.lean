@[expose] public section

universe uR uS uT v

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

variable (f : R →+* S) (hf : Function.Surjective f)

variable (hker : IsNilpotent (RingHom.ker f))

namespace K0

@[simp]
theorem equivOfSurjectiveOfIsNilpotentKer_symm_map (x : K0 R) :
    (equivOfSurjectiveOfIsNilpotentKer f hf hker).symm (map f x) = x := by
  simpa only [equivOfSurjectiveOfIsNilpotentKer_apply] using
    (equivOfSurjectiveOfIsNilpotentKer f hf hker).symm_apply_apply x

end K0
end KTheory
end
