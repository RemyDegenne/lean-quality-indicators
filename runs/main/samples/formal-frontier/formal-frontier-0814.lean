@[expose] public section

universe uR uS uT v

namespace KTheory

variable {R : Type uR} {S : Type uS} {T : Type uT}

variable [Ring R] [Ring S] [Ring T]

variable (f : R →+* S) (hf : Function.Surjective f)

variable (hker : IsNilpotent (RingHom.ker f))

namespace K0

theorem map_bijective_of_surjective_of_isNilpotent_ker
    (hf : Function.Surjective f) (hker : IsNilpotent (RingHom.ker f)) :
    Function.Bijective (map f) := by
  exact KTheory.K0.map_bijective_of_projectiveClass_map_bijective f
    (KTheory.ProjectiveClass.map_bijective_of_surjective_of_isNilpotent_ker f hf hker)

end K0
end KTheory
end
