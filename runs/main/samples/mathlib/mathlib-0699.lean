@[expose] public section

open Ideal Set SetLike

namespace DividedPowers

variable {A B : Type*} [CommSemiring A] [CommSemiring B] {I : Ideal A} {J : Ideal B}
  (hI : DividedPowers I) (hJ : DividedPowers J)

namespace IsDPMorphism

variable {hI hJ} {C : Type*} [CommSemiring C] {K : Ideal C} (hK : DividedPowers K)

theorem comp {f : A →+* B} {g : B →+* C} (hg : IsDPMorphism hJ hK g) (hf : IsDPMorphism hI hJ f) :
    IsDPMorphism hI hK (g.comp f) := by
  refine ⟨le_trans (map_map f g ▸ map_mono hf.1) hg.1, fun a ha ↦ ?_⟩
  simp only [RingHom.coe_comp, Function.comp_apply]
  rw [← hf.2 a ha, hg.2]
  exact hf.1 (mem_map_of_mem f ha)

end IsDPMorphism
end DividedPowers
end
