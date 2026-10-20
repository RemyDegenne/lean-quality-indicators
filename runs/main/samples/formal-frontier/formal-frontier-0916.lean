@[expose] public section

universe uR uS uM

open CategoryTheory CategoryTheory.Limits

namespace TopModuleCat

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable [TopologicalSpace R] [TopologicalSpace S]

variable (φ : R →+* S) (hφ : Continuous φ)

variable {M N : TopModuleCat.{uM} S} (f : M ⟶ N)

theorem restrictScalars_coker_existsUnique {P : TopModuleCat.{uM} R}
    (g : (restrictScalars φ hφ).obj N ⟶ P)
    (hg : (restrictScalars φ hφ).map f ≫ g = 0) :
    ∃! d : (restrictScalars φ hφ).obj (coker f) ⟶ P,
      (restrictScalars φ hφ).map (cokerπ f) ≫ d = g := by
  let hc := isColimitCoforkMapOfIsColimit' (restrictScalars φ hφ)
    (comp_cokerπ f) (isColimitCoker f)
  let s := CokernelCofork.ofπ g hg
  refine ⟨hc.desc s, hc.fac s WalkingParallelPair.one, ?_⟩
  intro d hd
  exact Cofork.IsColimit.hom_ext hc (hd.trans (hc.fac s WalkingParallelPair.one).symm)

end TopModuleCat
end
