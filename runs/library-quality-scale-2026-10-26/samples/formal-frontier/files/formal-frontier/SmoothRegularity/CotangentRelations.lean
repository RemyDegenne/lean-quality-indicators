/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.RingTheory.Extension.Cotangent.Basic
public import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
public import Mathlib.RingTheory.LocalRing.ResidueField.Ideal

/-!
# Selecting presentation relations in a cotangent kernel

This file selects a smallest linearly independent family among the relations
of a finite presentation whose images span the kernel of the base-changed
cotangent map.

Tensoring the right-exact cotangent sequence remains exact at its middle term.
The original finite relation family spans the conormal module, hence its
base-changed cotangent images span the kernel. Finite-dimensional linear
algebra then selects a family indexed by the kernel's dimension.
-/

public section

open scoped TensorProduct

namespace Algebra.Presentation

universe u v

variable {R : Type u} [CommRing R]
variable {S : Type v} [CommRing S] [Algebra R S]

/-- Over an arbitrary commutative base and at any prime of the target, select
from the relations of a finite presentation exactly the residue-field dimension
of the kernel of the base-changed cotangent map. Their images are linearly
independent and span that kernel. -/
theorem exists_relations_spanning_cotangentKernel {n r : ℕ}
    (P : Algebra.Presentation R S (Fin n) (Fin r)) (m : Ideal S) [m.IsPrime] :
    ∃ f : Fin (Module.finrank m.ResidueField
        (LinearMap.ker (P.toExtension.toKaehler.baseChange m.ResidueField))) → Fin r,
      Submodule.span m.ResidueField (Set.range fun i ↦
          (P.toExtension.cotangentComplex.baseChange m.ResidueField)
            (1 ⊗ₜ[S] Extension.Cotangent.mk
              ⟨P.relation (f i), P.relation_mem_ker (f i)⟩)) =
          LinearMap.ker (P.toExtension.toKaehler.baseChange m.ResidueField) ∧
        LinearIndependent m.ResidueField (fun i ↦
          (P.toExtension.cotangentComplex.baseChange m.ResidueField)
            (1 ⊗ₜ[S] Extension.Cotangent.mk
              ⟨P.relation (f i), P.relation_mem_ker (f i)⟩)) := by
  classical
  let relationCotangent : Fin r → P.toExtension.Cotangent := fun j ↦
    Extension.Cotangent.mk ⟨P.relation j, P.relation_mem_ker j⟩
  let relationBase : Fin r →
      (m.ResidueField) ⊗[S] P.toExtension.Cotangent := fun j ↦
    1 ⊗ₜ[S] relationCotangent j
  let relationImage : Fin r →
      (m.ResidueField) ⊗[S] P.toExtension.CotangentSpace := fun j ↦
    (P.toExtension.cotangentComplex.baseChange m.ResidueField) (relationBase j)
  let _ : Module.Finite m.ResidueField
      ((m.ResidueField) ⊗[S] P.toExtension.CotangentSpace) :=
    Module.Finite.of_basis (P.cotangentSpaceBasis.baseChange m.ResidueField)
  have hcotangent : Submodule.span S (Set.range relationCotangent) = ⊤ := by
    exact Extension.Cotangent.span_eq_top_of_span_eq_ker
      (P := P.toExtension) P.relation P.span_range_relation_eq_ker
  have hbase : Submodule.span m.ResidueField (Set.range relationBase) = ⊤ := by
    rw [show Set.range relationBase =
      TensorProduct.mk S m.ResidueField P.toExtension.Cotangent 1 ''
        Set.range relationCotangent by
          ext x
          constructor
          · rintro ⟨j, rfl⟩
            exact ⟨relationCotangent j, ⟨j, rfl⟩, rfl⟩
          · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
            exact ⟨j, rfl⟩]
    rw [← Submodule.baseChange_span, hcotangent, Submodule.baseChange_top]
  have hspan : Submodule.span m.ResidueField (Set.range relationImage) =
      LinearMap.ker (P.toExtension.toKaehler.baseChange m.ResidueField) := by
    calc
      Submodule.span m.ResidueField (Set.range relationImage) =
          LinearMap.range
            (P.toExtension.cotangentComplex.baseChange m.ResidueField) := by
        rw [show Set.range relationImage =
          (P.toExtension.cotangentComplex.baseChange m.ResidueField) ''
            Set.range relationBase by
              ext x
              constructor
              · rintro ⟨j, rfl⟩
                exact ⟨relationBase j, ⟨j, rfl⟩, rfl⟩
              · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
                exact ⟨j, rfl⟩]
        rw [← Submodule.map_span, hbase, Submodule.map_top]
      _ = LinearMap.ker
          (P.toExtension.toKaehler.baseChange m.ResidueField) := by
        have hex : Function.Exact
            (P.toExtension.cotangentComplex.baseChange m.ResidueField)
            (P.toExtension.toKaehler.baseChange m.ResidueField) :=
          lTensor_exact m.ResidueField
            P.toExtension.exact_cotangentComplex_toKaehler
            P.toExtension.toKaehler_surjective
        exact hex.linearMap_ker_eq.symm
  rw [← hspan]
  obtain ⟨g, hgmem, hgspan, hgindep⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq m.ResidueField
      (Set.range relationImage)
  choose f hf using hgmem
  refine ⟨f, ?_, ?_⟩
  · have hfun : (fun i ↦ relationImage (f i)) = g := by
      funext i
      exact hf i
    change Submodule.span m.ResidueField (Set.range fun i ↦ relationImage (f i)) = _
    rw [hfun, hgspan]
  · have hfun : (fun i ↦ relationImage (f i)) = g := by
      funext i
      exact hf i
    change LinearIndependent m.ResidueField (fun i ↦ relationImage (f i))
    rw [hfun]
    exact hgindep

end Algebra.Presentation
