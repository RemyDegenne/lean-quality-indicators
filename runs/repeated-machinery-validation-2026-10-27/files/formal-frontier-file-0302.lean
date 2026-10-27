/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProjectiveModules.KTheory.ScalarExtension
public import ProjectiveModules.KTheory.Trace

/-!
# Naturality of the Hattori–Stallings trace on K₀

Extension of scalars along a unital ring homomorphism commutes with the
Hattori–Stallings trace. The map on trace targets is Mathlib's additive
quotient map, applied to the additive commutator subgroups from
`GeneralLinearGroups.AdditiveCommutator`. These quotients are additive groups,
not ideal quotients or modules over the source ring.

`KTheory.K0 R` uses right `R`-modules, represented by left `Rᵐᵒᵖ`-modules;
the ring parameter in both the scalar-extension map and the trace is `R`.
The source and target rings have independent universes.
-/

set_option warningAsError true

@[expose] public section

universe uR uS

namespace KTheory.K0

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

/-- The Hattori–Stallings trace on right-module K₀ commutes with extension of
scalars along any unital ring homomorphism. On the additive commutator
quotients, the induced map sends the class of `r` to the class of `f r`. -/
theorem traceModCommutators_map (f : R →+* S) (z : K0 R) :
    traceModCommutators S (map f z) =
      QuotientAddGroup.map (Ring.additiveCommutators R) (Ring.additiveCommutators S)
        f.toAddMonoidHom (by
          change AddSubgroup.closure {x : R | ∃ a b : R, x = a * b - b * a} ≤ _
          apply (AddSubgroup.closure_le _).2
          rintro x ⟨a, b, rfl⟩
          change f (a * b - b * a) ∈ Ring.additiveCommutators S
          simpa only [map_sub, map_mul] using
            Ring.commutator_mem_additiveCommutators (f a) (f b))
        (traceModCommutators R z) := by
  classical
  let q : (R ⧸ Ring.additiveCommutators R) →+
      (S ⧸ Ring.additiveCommutators S) :=
    QuotientAddGroup.map (Ring.additiveCommutators R) (Ring.additiveCommutators S)
      f.toAddMonoidHom (by
        change AddSubgroup.closure {x : R | ∃ a b : R, x = a * b - b * a} ≤ _
        apply (AddSubgroup.closure_le _).2
        rintro x ⟨a, b, rfl⟩
        change f (a * b - b * a) ∈ Ring.additiveCommutators S
        simpa only [map_sub, map_mul] using
          Ring.commutator_mem_additiveCommutators (f a) (f b))
  change traceModCommutators S (map f z) = q (traceModCommutators R z)
  have hclass :
      (ProjectiveClass.traceModCommutators S).comp (ProjectiveClass.map f) =
        q.comp (ProjectiveClass.traceModCommutators R) := by
    apply ProjectiveClass.addHom_ext R
    intro X
    change ProjectiveClass.traceModCommutators S
        (ProjectiveClass.map f (ProjectiveClass.of R X)) =
      q (ProjectiveClass.traceModCommutators R (ProjectiveClass.of R X))
    rw [ProjectiveClass.map_of, ProjectiveClass.traceModCommutators_of_module,
      ProjectiveClass.traceModCommutators_of_module]
    -- Compute the identity trace using a finite free retract, not cancellation
    -- against the trace of a complementary module.
    obtain ⟨n, K, hKGroup, hKModule, _, ⟨e⟩⟩ :=
      Module.Projective.exists_finite_complement_linearEquiv (R := Rᵐᵒᵖ) (P := X)
    let _ : AddCommGroup K := hKGroup
    let _ : Module Rᵐᵒᵖ K := hKModule
    let e' : (X × K) ≃ₗ[Rᵐᵒᵖ] (Fin n → R) :=
      e.trans (Module.rightFreeCoordEquiv R (Fin n))
    let p : (Fin n → R) →ₗ[Rᵐᵒᵖ] X :=
      (LinearMap.fst Rᵐᵒᵖ X K).comp e'.symm.toLinearMap
    let s : X →ₗ[Rᵐᵒᵖ] (Fin n → R) :=
      e'.toLinearMap.comp (LinearMap.inl Rᵐᵒᵖ X K)
    have hps : p.comp s = LinearMap.id := by
      ext x
      simp [p, s]
    let E := ModuleCat.RightExtension.rightFreeLinearEquiv f (Fin n)
    let pS : (Fin n → S) →ₗ[Sᵐᵒᵖ] ModuleCat.RightExtension.Obj f X :=
      (ModuleCat.RightExtension.map f p).comp E.symm.toLinearMap
    let sS : ModuleCat.RightExtension.Obj f X →ₗ[Sᵐᵒᵖ] (Fin n → S) :=
      E.toLinearMap.comp (ModuleCat.RightExtension.map f s)
    have hpsS : pS.comp sS = LinearMap.id := by
      calc
        pS.comp sS = (ModuleCat.RightExtension.map f p).comp
            (ModuleCat.RightExtension.map f s) := by
          ext x
          simp [pS, sS]
        _ = ModuleCat.RightExtension.map f (p.comp s) :=
          (ModuleCat.RightExtension.map_comp f s p).symm
        _ = LinearMap.id := by rw [hps, ModuleCat.RightExtension.map_id]
    have hspS : sS.comp pS =
        Module.rightEndomorphismScalarExtension R (Fin n) f (s.comp p) := by
      rw [Module.rightEndomorphismScalarExtension_eq_tensor,
        ModuleCat.RightExtension.map_comp]
      ext x
      rfl
    let A := Module.rightEndomorphismMatrixEquiv R (Fin n) (s.comp p)
    have hR : LinearMap.traceModCommutators R X LinearMap.id =
        QuotientAddGroup.mk' (Ring.additiveCommutators R) (Matrix.trace A) := by
      rw [← hps, LinearMap.traceModCommutators_comp_comm R X s p,
        LinearMap.traceModCommutators_eq_matrix_trace]
    have hS : LinearMap.traceModCommutators S
        (ModuleCat.RightExtension.Obj f X) LinearMap.id =
        QuotientAddGroup.mk' (Ring.additiveCommutators S)
          (Matrix.trace (f.mapMatrix A)) := by
      rw [← hpsS,
        LinearMap.traceModCommutators_comp_comm S
          (ModuleCat.RightExtension.Obj f X) sS pS,
        hspS, LinearMap.traceModCommutators_eq_matrix_trace,
        ← Module.rightEndomorphismMatrixEquiv_scalarExtension]
    rw [hR, hS]
    change QuotientAddGroup.mk' (Ring.additiveCommutators S)
        (Matrix.trace (f.mapMatrix A)) =
      QuotientAddGroup.mk' (Ring.additiveCommutators S) (f (Matrix.trace A))
    congr 1
    exact (AddMonoidHom.map_trace f A).symm
  have hK0 : (traceModCommutators S).comp (map f) =
      q.comp (traceModCommutators R) := by
    apply hom_ext_ofClass R
    intro a
    change traceModCommutators S (map f (ofClass R a)) =
      q (traceModCommutators R (ofClass R a))
    rw [map_ofClass, traceModCommutators_ofClass, traceModCommutators_ofClass]
    exact DFunLike.congr_fun hclass a
  exact DFunLike.congr_fun hK0 z

end KTheory.K0
