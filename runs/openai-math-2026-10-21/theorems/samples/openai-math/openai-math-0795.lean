namespace OAI

noncomputable section

namespace ArExplicit

open CategoryTheory CompleteComparison

universe u

variable {R : Type u} [Ring R]

variable {P : ChainComplex (ModuleCat.{u} R) ℤ}

variable {N : Type u} [AddCommGroup N] [Module R N]

theorem completeExtCocycleMap_stable_zero_iff (hP : TotallyAcyclicComplex P)
    (n : ℤ) (f : P.X n →ₗ[R] N) (hf : f.comp (P.d (n + 1) n).hom = 0) :
    StableHom.classOf R _ N (completeExtCocycleMap n f hf) = 0 ↔
      ∃ g : P.X (n - 1) →ₗ[R] N, g.comp (P.d n (n - 1)).hom = f := by
  rw [StableHom.classOf_eq_zero_iff_projective]
  constructor
  · rintro ⟨Q, hQ, hRQ, hproj, hfin, i, p, hip⟩
    let π := (LinearMap.range (P.d (n + 1) n).hom).mkQ
    have hi : (i.comp π).comp (P.d (n + 1) n).hom = 0 := by
      rw [LinearMap.comp_assoc, LinearMap.range_mkQ_comp, LinearMap.comp_zero]
    obtain ⟨g, hg⟩ := (hP.dualExact n).projective (i.comp π) hi
    refine ⟨p.comp g, ?_⟩
    rw [LinearMap.comp_assoc, hg, ← LinearMap.comp_assoc, hip]
    rfl
  · rintro ⟨g, hg⟩
    let := hP.finite (n - 1)
    let := hP.projective (n - 1)
    let d : Cokernel P n →ₗ[R] P.X (n - 1) :=
      completeExtCocycleMap n (P.d n (n - 1)).hom (differential_comp P _ _ _)
    refine ⟨P.X (n - 1), inferInstance, inferInstance, inferInstance, inferInstance, d, g, ?_⟩
    apply LinearMap.ext
    intro x
    obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (LinearMap.range (P.d (n + 1) n).hom) x
    exact DFunLike.congr_fun hg x

end ArExplicit
end
end OAI
