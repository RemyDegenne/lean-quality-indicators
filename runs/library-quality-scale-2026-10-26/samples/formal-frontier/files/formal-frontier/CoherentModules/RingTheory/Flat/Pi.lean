/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import CoherentModules.LinearAlgebra.Pi
public import CoherentModules.RingTheory.Flat.FaithfullyFlat
public import Mathlib.LinearAlgebra.TensorProduct.Quotient

/-!
# Faithful flatness of products of algebras

An arbitrary dependent product of unital algebras is faithfully flat if and only
if the whole product is flat and every finitely generated proper ideal has a
nontrivial quotient-tensor fiber in some component. The component may depend on
the ideal. The algebras need not be commutative.

Neither flatness of every component nor coordinate detection of every proper
ideal can be substituted silently: infinite products need not be flat, and
quotient tensors need not commute with arbitrary products for ideals that are
not finitely generated. The coefficient ring, index and algebra carriers have
independent universes; empty products and subsingleton rings are allowed.

## References

The characterization uses the finitely generated ideal criterion for unital
algebras, multiplication of finitely generated ideals through dependent products,
and Mathlib's quotient-tensor equivalence.
-/

@[expose] public section

open scoped TensorProduct

universe u v w

namespace Module.FaithfullyFlat

/-- An arbitrary product of unital algebras is faithfully flat exactly when the
whole product is flat and every finitely generated proper ideal has a nontrivial
quotient-tensor fiber in some component. The algebras may be noncommutative, and
no finiteness assumption is made on the index. -/
theorem pi_algebra_iff
    (R : Type u) [CommRing R] {ι : Type v} (A : ι → Type w)
    [∀ i, Ring (A i)] [∀ i, Algebra R (A i)] :
    Module.FaithfullyFlat R (Π i, A i) ↔
      Module.Flat R (Π i, A i) ∧
        ∀ I : Ideal R, I.FG → I ≠ ⊤ →
          ∃ i, Nontrivial ((R ⧸ I) ⊗[R] A i) := by
  classical
  rw [algebra_iff_flat_and_fg_proper_ideal R (Π i, A i)]
  refine and_congr_right fun _ ↦ forall_congr' fun I ↦
    imp_congr_right fun hI ↦ imp_congr_right fun _ ↦ ?_
  have hsmul : I • (⊤ : Submodule R (Π i, A i)) =
      Submodule.pi Set.univ (fun i ↦ I • (⊤ : Submodule R (A i))) := by
    simpa only [Submodule.pi_top] using
      Submodule.smul_pi_of_fg I hI (fun i ↦ (⊤ : Submodule R (A i)))
  have hpi :
      Submodule.pi Set.univ (fun i ↦ I • (⊤ : Submodule R (A i))) = ⊤ ↔
        ∀ i, I • (⊤ : Submodule R (A i)) = ⊤ := by
    constructor
    · intro h i
      apply top_unique
      intro x _
      have hx : Pi.single i x ∈
          Submodule.pi Set.univ (fun i ↦ I • (⊤ : Submodule R (A i))) := by
        rw [h]
        exact Submodule.mem_top
      simpa only [Pi.single_eq_same] using
        (Submodule.mem_pi.mp hx i (Set.mem_univ i))
    · intro h
      simp only [h, Submodule.pi_top]
  rw [hsmul, ne_eq, hpi, not_forall]
  exact exists_congr fun i ↦ Submodule.Quotient.nontrivial_iff.symm.trans <|
    (TensorProduct.quotTensorEquivQuotSMul (A i) I).toEquiv.nontrivial_congr.symm

end Module.FaithfullyFlat
