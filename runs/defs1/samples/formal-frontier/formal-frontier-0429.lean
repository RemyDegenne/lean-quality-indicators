set_option warningAsError true

@[expose] public section

universe u v w v' w'

open CategoryTheory ContinuousMap

namespace ContinuousMap

variable {k : Type u} [Semiring k] [TopologicalSpace k]

variable {G : Type v} [TopologicalSpace G]

variable {M : Type w} [TopologicalSpace M] [AddCommMonoid M] [Module k M]
  [ContinuousAdd M] [ContinuousSMul k M]

/-- Raising a continuous-function space is continuously linearly equivalent to
the continuous-function space between independently raised source and target
types. -/
noncomputable def uliftContinuousLinearEquiv :
    ULift.{max v' w'} C(G, M) ≃L[k] C(ULift.{v'} G, ULift.{w'} M) :=
  let downG : C(ULift.{v'} G, G) := ⟨ULift.down, continuous_uliftDown⟩
  let upG : C(G, ULift.{v'} G) := ⟨ULift.up, continuous_uliftUp⟩
  let downM : C(ULift.{w'} M, M) := ⟨ULift.down, continuous_uliftDown⟩
  let upM : C(M, ULift.{w'} M) := ⟨ULift.up, continuous_uliftUp⟩
  let eMaps : ULift.{max v' w'} C(G, M) ≃L[k] C(G, M) :=
    ContinuousLinearEquiv.ulift
  ContinuousLinearEquiv.mk
    { toFun := fun F =>
        upM.comp (F.down.comp downG)
      invFun := fun F =>
        ULift.up (downM.comp (F.comp upG))
      left_inv := fun F => by ext x; simp [downG, upG, downM, upM]
      right_inv := fun F => by ext x; simp [downG, upG, downM, upM]
      map_add' := fun F H => by ext x; simp [downG, upM]
      map_smul' := fun r F => by ext x; simp [downG, upM] }
    (by
      change Continuous (fun F : ULift.{max v' w'} C(G, M) =>
        upM.comp (F.down.comp downG))
      exact (continuous_postcomp upM).comp
        ((continuous_precomp downG).comp eMaps.continuous))
    (by
      change Continuous (fun F : C(ULift.{v'} G, ULift.{w'} M) =>
        ULift.up (downM.comp (F.comp upG)))
      exact eMaps.symm.continuous.comp
        ((continuous_postcomp downM).comp (continuous_precomp upG)))

end ContinuousMap
end
