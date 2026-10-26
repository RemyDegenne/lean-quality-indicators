/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.AdicCompletion.Completeness
public import Mathlib.Topology.Algebra.Nonarchimedean.AdicTopology

/-!
# Evaluation neighborhoods in an adic completion

For a finitely generated ideal, evaluation kernels form a zero-neighborhood basis in
Mathlib's adic module topology on the existing completion. Finite generation is needed
only for the ideal, not for the module. All natural precisions, including zero, occur.
This statement concerns the specified adic topology; no separate product-topology
identification or new inverse-limit construction is asserted here.

## References

* Mathlib's adic topology construction by Patrick Massot.
* Bingyu Xia's `AdicCompletion.pow_smul_top_eq_ker_eval` in Mathlib, identifying the
  ideal-power submodules of the completion with its evaluation kernels.
-/

@[expose] public section

universe u v

namespace AdicCompletion

/-- Evaluation kernels form a zero-neighborhood basis for the adic module topology
on the completion of an arbitrary module at a finitely generated ideal. -/
theorem hasBasis_nhds_zero_ker_eval
    {R : Type u} [CommRing R] (I : Ideal R)
    (M : Type v) [AddCommGroup M] [Module R M] (hI : I.FG) :
    (@nhds (AdicCompletion I M) (I.adicModuleTopology (AdicCompletion I M)) 0).HasBasis
      (fun _n : ℕ ↦ True)
      (fun n ↦ ((eval I M n).ker : Set (AdicCompletion I M))) := by
  let : TopologicalSpace R := I.adicTopology
  refine ⟨fun U ↦ ?_⟩
  rw [(I.ringFilterBasis.moduleFilterBasis
    (I.adic_module_basis (AdicCompletion I M))).toAddGroupFilterBasis.nhds_zero_hasBasis.mem_iff]
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, hn⟩
    exact ⟨n, trivial, by simpa only [id_eq, pow_smul_top_eq_ker_eval hI] using hn⟩
  · rintro ⟨n, -, hn⟩
    refine ⟨_, ⟨n, rfl⟩, ?_⟩
    simpa only [id_eq, pow_smul_top_eq_ker_eval hI] using hn

end AdicCompletion
