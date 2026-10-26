/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import AlgebraicDirectLimits.Topology.TensorHom
public import Mathlib.LinearAlgebra.TensorProduct.Associator

/-!
# Associativity of one-sided topological tensors

Two algebraic coefficient modules and a supplied topological module can be
reassociated by Mathlib's algebraic tensor associator. The coefficient modules
carry no topology. Both parenthesizations use `TopModuleCat.tensorLeftObj`, so
addition and the joint scalar action come from the existing tensor construction.
The scalar ring and the three module carriers have independent universes.

The characteristic API records exact algebraic agreement, forward and inverse
pure-tensor formulas, composition with generators, uniqueness and naturality in
both algebraic coefficient maps and the continuous right-factor map.

## References

Mathlib's tensor associator and tensor-map API are due to Kenny Lau and Mario
Carneiro. The one-sided topology and generators are Formal Frontier Agents' ADL
development, following Beacon's topological ideas. Mathlib's topological-module
category and coinduced construction are due to Richard Hill and Andrew Yang.
The continuous-linear-equivalence API is due to Jan-David Salchow, Sébastien
Gouëzel, Jean Lo, Yury Kudryashov, Frédéric Dupuis and Heather Macbeth.
-/

@[expose] public section

open scoped TensorProduct

universe uR uC uD uM uC' uD' uN

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R) (M : TopModuleCat.{uM} R)

/-- Reassociate two algebraic coefficient modules and a supplied topological
right factor, using exactly Mathlib's algebraic tensor associator. -/
noncomputable def tensorAssocContinuousLinearEquiv :
    tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M ≃L[R]
      tensorLeftObj R C (tensorLeftObj R D M) where
  toLinearEquiv :=
    (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M ≃ₗ[R]
      tensorLeftObj R C (tensorLeftObj R D M) from TensorProduct.assoc R C D M)
  continuous_toFun := by
    apply (continuous_tensorLeftObj_iff_tmul R (ModuleCat.of R (C ⊗[R] D)) M
      (tensorLeftObj R C (tensorLeftObj R D M))
      (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M →ₗ[R]
        tensorLeftObj R C (tensorLeftObj R D M) from
          (TensorProduct.assoc R C D M).toLinearMap)).mpr
    intro z
    induction z using TensorProduct.inductionOn with
    | tmul c d =>
      refine ((tensorGenerator R C (tensorLeftObj R D M) c).continuous.comp
        (tensorGenerator R D M d).continuous).congr ?_
      intro m
      change (tensorGenerator R C (tensorLeftObj R D M) c)
        (tensorGenerator R D M d m) =
          (TensorProduct.assoc R C D M) ((c ⊗ₜ[R] d) ⊗ₜ[R] m)
      -- Keep the intermediate tensors in the supplied carriers.
      have hinner : tensorGenerator R D M d m =
          (show tensorLeftObj R D M from d ⊗ₜ[R] m) :=
        tensorGenerator_apply R D M d m
      have houter :
          (tensorGenerator R C (tensorLeftObj R D M) c)
            (show tensorLeftObj R D M from d ⊗ₜ[R] m) =
          (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
        tensorGenerator_apply R C (tensorLeftObj R D M) c
          (show tensorLeftObj R D M from d ⊗ₜ[R] m)
      have hassoc :
          (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) =
            (TensorProduct.assoc R C D M) ((c ⊗ₜ[R] d) ⊗ₜ[R] m) :=
        (TensorProduct.assoc_tmul (R := R) c d m).symm
      exact Eq.trans (congrArg (tensorGenerator R C (tensorLeftObj R D M) c) hinner)
        (Eq.trans houter hassoc)
    | add x y hx hy =>
      refine (hx.add hy).congr ?_
      intro m
      change (TensorProduct.assoc R C D M).toLinearMap (x ⊗ₜ[R] m) +
        (TensorProduct.assoc R C D M).toLinearMap (y ⊗ₜ[R] m) =
          (TensorProduct.assoc R C D M).toLinearMap ((x + y) ⊗ₜ[R] m)
      calc
        _ = (TensorProduct.assoc R C D M).toLinearMap
            (x ⊗ₜ[R] m + y ⊗ₜ[R] m) :=
          ((TensorProduct.assoc R C D M).toLinearMap.map_add
            (x ⊗ₜ[R] m) (y ⊗ₜ[R] m)).symm
        _ = _ := congrArg (TensorProduct.assoc R C D M).toLinearMap
          (TensorProduct.add_tmul (R := R) x y m).symm
  continuous_invFun := by
    apply (continuous_tensorLeftObj_iff_tmul R C (tensorLeftObj R D M)
      (tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M)
      (show tensorLeftObj R C (tensorLeftObj R D M) →ₗ[R]
        tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (TensorProduct.assoc R C D M).symm.toLinearMap)).mpr
    intro c
    apply (continuous_tensorLeftObj_iff_tmul R D M
      (tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M)
      (show tensorLeftObj R D M →ₗ[R]
        tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (TensorProduct.assoc R C D M).symm.toLinearMap.comp
            ((TensorProduct.mk R C (tensorLeftObj R D M)) c))).mpr
    intro d
    refine (tensorGenerator R (ModuleCat.of R (C ⊗[R] D)) M
      (c ⊗ₜ[R] d)).continuous.congr ?_
    intro m
    -- Form the restriction identity in the supplied flat carrier.
    have hgenerator :
        tensorGenerator R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d) m =
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (c ⊗ₜ[R] d) ⊗ₜ[R] m) :=
      tensorGenerator_apply R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d) m
    have hassoc :
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (c ⊗ₜ[R] d) ⊗ₜ[R] m) =
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (TensorProduct.assoc R C D M).symm.toLinearMap
            (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m))) :=
      (TensorProduct.assoc_symm_tmul (R := R) c d m).symm
    have hmk :
        ((TensorProduct.mk R C (tensorLeftObj R D M)) c)
            (show tensorLeftObj R D M from d ⊗ₜ[R] m) =
          (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
      TensorProduct.mk_apply (R := R) c (show tensorLeftObj R D M from d ⊗ₜ[R] m)
    have hcomp :
        ((TensorProduct.assoc R C D M).symm.toLinearMap.comp
          ((TensorProduct.mk R C (tensorLeftObj R D M)) c))
            (show tensorLeftObj R D M from d ⊗ₜ[R] m) =
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (TensorProduct.assoc R C D M).symm.toLinearMap
            (((TensorProduct.mk R C (tensorLeftObj R D M)) c)
              (show tensorLeftObj R D M from d ⊗ₜ[R] m))) :=
      LinearMap.comp_apply (TensorProduct.assoc R C D M).symm.toLinearMap
        ((TensorProduct.mk R C (tensorLeftObj R D M)) c)
        (show tensorLeftObj R D M from d ⊗ₜ[R] m)
    have hrestriction :
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (TensorProduct.assoc R C D M).symm.toLinearMap
            (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m))) =
        ((TensorProduct.assoc R C D M).symm.toLinearMap.comp
          ((TensorProduct.mk R C (tensorLeftObj R D M)) c))
            (show tensorLeftObj R D M from d ⊗ₜ[R] m) :=
      (Eq.trans hcomp
        (congrArg (fun y : tensorLeftObj R C (tensorLeftObj R D M) ↦
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (TensorProduct.assoc R C D M).symm.toLinearMap y)) hmk)).symm
    exact Eq.trans hgenerator (Eq.trans hassoc hrestriction)

/-- Forgetting continuity gives the algebraic tensor associator. -/
@[simp]
theorem tensorAssocContinuousLinearEquiv_toLinearEquiv :
    (tensorAssocContinuousLinearEquiv R C D M).toLinearEquiv =
      (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M ≃ₗ[R]
        tensorLeftObj R C (tensorLeftObj R D M) from TensorProduct.assoc R C D M) := rfl

/-- The forward underlying linear map is Mathlib's algebraic associator. -/
@[simp]
theorem tensorAssocContinuousLinearEquiv_toLinearMap :
    (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap.toLinearMap =
      (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M →ₗ[R]
        tensorLeftObj R C (tensorLeftObj R D M) from
          (TensorProduct.assoc R C D M).toLinearMap) := rfl

/-- The inverse underlying equivalence is the inverse algebraic associator. -/
@[simp]
theorem tensorAssocContinuousLinearEquiv_symm_toLinearEquiv :
    (tensorAssocContinuousLinearEquiv R C D M).symm.toLinearEquiv =
      (show tensorLeftObj R C (tensorLeftObj R D M) ≃ₗ[R]
        tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (TensorProduct.assoc R C D M).symm) := by
  rfl

/-- On every tensor, reassociation agrees with the algebraic associator. -/
theorem tensorAssocContinuousLinearEquiv_apply
    (x : tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M) :
    tensorAssocContinuousLinearEquiv R C D M x = TensorProduct.assoc R C D M x := by
  rfl

/-- On every nested tensor, inverse reassociation agrees with the algebraic inverse. -/
theorem tensorAssocContinuousLinearEquiv_symm_apply
    (y : tensorLeftObj R C (tensorLeftObj R D M)) :
    (tensorAssocContinuousLinearEquiv R C D M).symm y =
      (TensorProduct.assoc R C D M).symm y := by
  rfl

/-- Reassociation sends a left-parenthesized pure triple to the nested pure triple. -/
@[simp]
theorem tensorAssocContinuousLinearEquiv_tmul (c : C) (d : D) (m : M) :
    tensorAssocContinuousLinearEquiv R C D M ((c ⊗ₜ[R] d) ⊗ₜ[R] m) =
      c ⊗ₜ[R] (d ⊗ₜ[R] m) := by
  exact (tensorAssocContinuousLinearEquiv_apply R C D M
    (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
      (c ⊗ₜ[R] d) ⊗ₜ[R] m)).trans
        (TensorProduct.assoc_tmul (R := R) c d m)

/-- Inverse reassociation reverses the pure-triple formula. -/
@[simp]
theorem tensorAssocContinuousLinearEquiv_symm_tmul (c : C) (d : D) (m : M) :
    (tensorAssocContinuousLinearEquiv R C D M).symm (c ⊗ₜ[R] (d ⊗ₜ[R] m)) =
      (c ⊗ₜ[R] d) ⊗ₜ[R] m := by
  exact (tensorAssocContinuousLinearEquiv_symm_apply R C D M
    (show tensorLeftObj R C (tensorLeftObj R D M) from
      c ⊗ₜ[R] (d ⊗ₜ[R] m))).trans
        (TensorProduct.assoc_symm_tmul (R := R) c d m)

/-- The associator carries the generator at `c ⊗ d` to the composite of the
inner generator at `d` and the outer generator at `c`. -/
theorem tensorAssocContinuousLinearEquiv_comp_tensorGenerator (c : C) (d : D) :
    (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap.comp
        (tensorGenerator R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d)) =
      (tensorGenerator R C (tensorLeftObj R D M) c).comp (tensorGenerator R D M d) := by
  apply ContinuousLinearMap.ext
  intro m
  have hflat :
      tensorGenerator R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d) m =
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (c ⊗ₜ[R] d) ⊗ₜ[R] m) :=
    tensorGenerator_apply R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d) m
  have hinner : tensorGenerator R D M d m =
      (show tensorLeftObj R D M from d ⊗ₜ[R] m) :=
    tensorGenerator_apply R D M d m
  have houter :
      (tensorGenerator R C (tensorLeftObj R D M) c)
          (show tensorLeftObj R D M from d ⊗ₜ[R] m) =
        (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
    tensorGenerator_apply R C (tensorLeftObj R D M) c
      (show tensorLeftObj R D M from d ⊗ₜ[R] m)
  have hnested :
      ((tensorGenerator R C (tensorLeftObj R D M) c).comp
        (tensorGenerator R D M d)) m =
      (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
    Eq.trans (ContinuousLinearMap.comp_apply
      (tensorGenerator R C (tensorLeftObj R D M) c) (tensorGenerator R D M d) m)
      (Eq.trans (congrArg (tensorGenerator R C (tensorLeftObj R D M) c) hinner) houter)
  have hassoc :
      tensorAssocContinuousLinearEquiv R C D M
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (c ⊗ₜ[R] d) ⊗ₜ[R] m) =
        (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
    tensorAssocContinuousLinearEquiv_tmul R C D M c d m
  have hforward :
      ((tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap.comp
        (tensorGenerator R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d))) m =
      (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
    Eq.trans (ContinuousLinearMap.comp_apply
      (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap
      (tensorGenerator R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d)) m)
      (Eq.trans (ContinuousLinearEquiv.coe_apply (tensorAssocContinuousLinearEquiv R C D M) _)
        (Eq.trans (congrArg (tensorAssocContinuousLinearEquiv R C D M) hflat) hassoc))
  exact Eq.trans hforward hnested.symm

/-- Inverse reassociation carries the composite of the two nested generators
back to the generator at `c ⊗ d`. -/
theorem tensorAssocContinuousLinearEquiv_symm_comp_tensorGenerator (c : C) (d : D) :
    (tensorAssocContinuousLinearEquiv R C D M).symm.toContinuousLinearMap.comp
        ((tensorGenerator R C (tensorLeftObj R D M) c).comp (tensorGenerator R D M d)) =
      tensorGenerator R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d) := by
  apply ContinuousLinearMap.ext
  intro m
  have hinner : tensorGenerator R D M d m =
      (show tensorLeftObj R D M from d ⊗ₜ[R] m) :=
    tensorGenerator_apply R D M d m
  have houter :
      (tensorGenerator R C (tensorLeftObj R D M) c)
          (show tensorLeftObj R D M from d ⊗ₜ[R] m) =
        (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
    tensorGenerator_apply R C (tensorLeftObj R D M) c
      (show tensorLeftObj R D M from d ⊗ₜ[R] m)
  have hnested :
      ((tensorGenerator R C (tensorLeftObj R D M) c).comp
        (tensorGenerator R D M d)) m =
      (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
    Eq.trans (ContinuousLinearMap.comp_apply
      (tensorGenerator R C (tensorLeftObj R D M) c) (tensorGenerator R D M d) m)
      (Eq.trans (congrArg (tensorGenerator R C (tensorLeftObj R D M) c) hinner) houter)
  have hassoc :
      (tensorAssocContinuousLinearEquiv R C D M).symm
          (show tensorLeftObj R C (tensorLeftObj R D M) from c ⊗ₜ[R] (d ⊗ₜ[R] m)) =
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (c ⊗ₜ[R] d) ⊗ₜ[R] m) :=
    tensorAssocContinuousLinearEquiv_symm_tmul R C D M c d m
  have hflat :
      tensorGenerator R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d) m =
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (c ⊗ₜ[R] d) ⊗ₜ[R] m) :=
    tensorGenerator_apply R (ModuleCat.of R (C ⊗[R] D)) M (c ⊗ₜ[R] d) m
  exact Eq.trans (ContinuousLinearMap.comp_apply
    (tensorAssocContinuousLinearEquiv R C D M).symm.toContinuousLinearMap
    ((tensorGenerator R C (tensorLeftObj R D M) c).comp (tensorGenerator R D M d)) m)
    (Eq.trans (ContinuousLinearEquiv.coe_apply (tensorAssocContinuousLinearEquiv R C D M).symm _)
      (Eq.trans (congrArg (tensorAssocContinuousLinearEquiv R C D M).symm hnested)
        (Eq.trans hassoc hflat.symm)))

/-- Continuous linear maps out of a left-parenthesized triple tensor are determined
by their values on all pure triples. The target has an independent universe. -/
@[ext]
theorem tensorAssoc_ext {N : TopModuleCat.{uN} R}
    {f g : tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M →L[R] N}
    (h : ∀ c d m, f ((c ⊗ₜ[R] d) ⊗ₜ[R] m) = g ((c ⊗ₜ[R] d) ⊗ₜ[R] m)) :
    f = g := by
  apply ContinuousLinearMap.coe_injective
  exact TensorProduct.ext_threefold h

/-- The pure-triple formula uniquely characterizes the continuous associator. -/
theorem tensorAssocContinuousLinearEquiv_unique
    (e : tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M ≃L[R]
      tensorLeftObj R C (tensorLeftObj R D M))
    (he : ∀ c d m, e ((c ⊗ₜ[R] d) ⊗ₜ[R] m) = c ⊗ₜ[R] (d ⊗ₜ[R] m)) :
    e = tensorAssocContinuousLinearEquiv R C D M := by
  apply ContinuousLinearEquiv.coe_injective
  apply tensorAssoc_ext R C D M
  intro c d m
  exact (he c d m).trans (tensorAssocContinuousLinearEquiv_tmul R C D M c d m).symm

/-- Reassociation is natural for both algebraic coefficient maps and a continuous
linear map on the supplied right factor. -/
theorem tensorAssocContinuousLinearEquiv_naturality
    {C' : ModuleCat.{uC'} R} {D' : ModuleCat.{uD'} R} {N : TopModuleCat.{uN} R}
    (f : C →ₗ[R] C') (g : D →ₗ[R] D') (h : M →L[R] N) :
    (tensorMapCLM R f (tensorMapCLM R g h)).comp
        (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap =
      (tensorAssocContinuousLinearEquiv R C' D' N).toContinuousLinearMap.comp
        (tensorMapCLM R
          (C := ModuleCat.of R (C ⊗[R] D))
          (D := ModuleCat.of R (C' ⊗[R] D')) (TensorProduct.map f g) h) := by
  apply tensorAssoc_ext R C D M
  intro c d m
  -- Forget the maps through their API and use algebraic naturality on this input.
  have hmap :
      (tensorMapCLM R f (tensorMapCLM R g h)).toLinearMap =
        (show tensorLeftObj R C (tensorLeftObj R D M) →ₗ[R]
          tensorLeftObj R C' (tensorLeftObj R D' N) from
            TensorProduct.map f (TensorProduct.map g h.toLinearMap)) :=
    Eq.trans (tensorMapCLM_toLinearMap R f (tensorMapCLM R g h))
      (congrArg (fun k : tensorLeftObj R D M →ₗ[R] tensorLeftObj R D' N ↦
        (show tensorLeftObj R C (tensorLeftObj R D M) →ₗ[R]
          tensorLeftObj R C' (tensorLeftObj R D' N) from TensorProduct.map f k))
        (tensorMapCLM_toLinearMap R g h))
  have hflat :
      tensorMapCLM R
        (C := ModuleCat.of R (C ⊗[R] D))
        (D := ModuleCat.of R (C' ⊗[R] D')) (TensorProduct.map f g) h
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (c ⊗ₜ[R] d) ⊗ₜ[R] m) =
      (show tensorLeftObj R (ModuleCat.of R (C' ⊗[R] D')) N from
        TensorProduct.map (TensorProduct.map f g) h.toLinearMap ((c ⊗ₜ[R] d) ⊗ₜ[R] m)) :=
    tensorMapCLM_apply R
      (C := ModuleCat.of R (C ⊗[R] D))
      (D := ModuleCat.of R (C' ⊗[R] D')) (TensorProduct.map f g) h _
  have hleft :
      ((tensorMapCLM R f (tensorMapCLM R g h)).comp
        (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap)
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (c ⊗ₜ[R] d) ⊗ₜ[R] m) =
      (show tensorLeftObj R C' (tensorLeftObj R D' N) from
        TensorProduct.map f (TensorProduct.map g h.toLinearMap)
          (TensorProduct.assoc R C D M ((c ⊗ₜ[R] d) ⊗ₜ[R] m))) :=
    Eq.trans (ContinuousLinearMap.comp_apply (tensorMapCLM R f (tensorMapCLM R g h))
      (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap
      (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
        (c ⊗ₜ[R] d) ⊗ₜ[R] m))
      (Eq.trans (congrArg (tensorMapCLM R f (tensorMapCLM R g h))
        (ContinuousLinearEquiv.coe_apply (tensorAssocContinuousLinearEquiv R C D M) _))
        (Eq.trans (congrArg (tensorMapCLM R f (tensorMapCLM R g h))
          (tensorAssocContinuousLinearEquiv_apply R C D M
            (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
              (c ⊗ₜ[R] d) ⊗ₜ[R] m)))
          (DFunLike.congr_fun hmap
            (show tensorLeftObj R C (tensorLeftObj R D M) from
              TensorProduct.assoc R C D M ((c ⊗ₜ[R] d) ⊗ₜ[R] m)))))
  have halgebraic :
      (show tensorLeftObj R C' (tensorLeftObj R D' N) from
        TensorProduct.map f (TensorProduct.map g h.toLinearMap)
          (TensorProduct.assoc R C D M ((c ⊗ₜ[R] d) ⊗ₜ[R] m))) =
      (show tensorLeftObj R C' (tensorLeftObj R D' N) from
        TensorProduct.assoc R C' D' N
          (TensorProduct.map (TensorProduct.map f g) h.toLinearMap ((c ⊗ₜ[R] d) ⊗ₜ[R] m))) :=
    TensorProduct.map_map_assoc f g h.toLinearMap ((c ⊗ₜ[R] d) ⊗ₜ[R] m)
  have hright :
      ((tensorAssocContinuousLinearEquiv R C' D' N).toContinuousLinearMap.comp
        (tensorMapCLM R
          (C := ModuleCat.of R (C ⊗[R] D))
          (D := ModuleCat.of R (C' ⊗[R] D')) (TensorProduct.map f g) h))
            (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
              (c ⊗ₜ[R] d) ⊗ₜ[R] m) =
      (show tensorLeftObj R C' (tensorLeftObj R D' N) from
        TensorProduct.assoc R C' D' N
          (TensorProduct.map (TensorProduct.map f g) h.toLinearMap ((c ⊗ₜ[R] d) ⊗ₜ[R] m))) :=
    Eq.trans (ContinuousLinearMap.comp_apply
      (tensorAssocContinuousLinearEquiv R C' D' N).toContinuousLinearMap
      (tensorMapCLM R
        (C := ModuleCat.of R (C ⊗[R] D))
        (D := ModuleCat.of R (C' ⊗[R] D')) (TensorProduct.map f g) h)
      (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
        (c ⊗ₜ[R] d) ⊗ₜ[R] m))
      (Eq.trans (ContinuousLinearEquiv.coe_apply (tensorAssocContinuousLinearEquiv R C' D' N) _)
        (Eq.trans (congrArg (tensorAssocContinuousLinearEquiv R C' D' N) hflat)
          (tensorAssocContinuousLinearEquiv_apply R C' D' N
            (show tensorLeftObj R (ModuleCat.of R (C' ⊗[R] D')) N from
              TensorProduct.map (TensorProduct.map f g) h.toLinearMap
                ((c ⊗ₜ[R] d) ⊗ₜ[R] m)))))
  exact Eq.trans hleft (Eq.trans halgebraic hright.symm)

end TopModuleCat

namespace TopModuleCat

section LiftCurry

/-- Lifting a family linear in two algebraic coefficients agrees with iterated
continuous lifting followed by tensor reassociation. -/
theorem tensorLiftCLM_lift_eq_comp_tensorAssoc
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R)
    (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R)
    (b : C →ₗ[R] D →ₗ[R] (M →L[R] N)) :
    (tensorLiftCLM R
      (C := ModuleCat.of R (C ⊗[R] D)) (M := M) (N := N)
      (TensorProduct.lift b) :
        tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M →L[R] N) =
      (tensorLiftCLM R (C := C) (M := tensorLeftObj R D M) (N := N)
        ((tensorHomLinearEquiv R D M N).symm.toLinearMap.comp b)).comp
          (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap := by
  apply tensorAssoc_ext R C D M
  intro c d m
  have hflat :
      tensorLiftCLM R
          (C := ModuleCat.of R (C ⊗[R] D)) (M := M) (N := N)
          (TensorProduct.lift b)
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (c ⊗ₜ[R] d) ⊗ₜ[R] m) = b c d m :=
    (tensorLiftCLM_tmul R
      (C := ModuleCat.of R (C ⊗[R] D)) (M := M) (N := N)
      (TensorProduct.lift b) (c ⊗ₜ[R] d) m).trans
        (congrArg (fun k : M →L[R] N ↦ k m)
          (TensorProduct.lift.tmul (f' := b) c d))
  have hnested :
      tensorLiftCLM R (C := C) (M := tensorLeftObj R D M) (N := N)
          ((tensorHomLinearEquiv R D M N).symm.toLinearMap.comp b)
          (show tensorLeftObj R C (tensorLeftObj R D M) from
            c ⊗ₜ[R] (d ⊗ₜ[R] m)) = b c d m := by
    calc
      _ = ((tensorHomLinearEquiv R D M N).symm.toLinearMap.comp b) c
          (show tensorLeftObj R D M from d ⊗ₜ[R] m) :=
        tensorLiftCLM_tmul R (C := C) (M := tensorLeftObj R D M) (N := N)
          ((tensorHomLinearEquiv R D M N).symm.toLinearMap.comp b) c
          (show tensorLeftObj R D M from d ⊗ₜ[R] m)
      _ = (tensorHomLinearEquiv R D M N).symm (b c)
          (show tensorLeftObj R D M from d ⊗ₜ[R] m) :=
        congrArg (fun k : tensorLeftObj R D M →L[R] N ↦
          k (show tensorLeftObj R D M from d ⊗ₜ[R] m))
          ((LinearMap.comp_apply
            (tensorHomLinearEquiv R D M N).symm.toLinearMap b c).trans
              (congrFun (LinearEquiv.coe_toLinearMap
                (tensorHomLinearEquiv R D M N).symm) (b c)))
      _ = b c d m := tensorHomLinearEquiv_symm_apply_tmul R
        (C := D) (M := M) (N := N) (b c) d m
  have hassoc :
      (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (c ⊗ₜ[R] d) ⊗ₜ[R] m) =
        (show tensorLeftObj R C (tensorLeftObj R D M) from
          c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
    (ContinuousLinearEquiv.coe_apply (tensorAssocContinuousLinearEquiv R C D M)
      (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
        (c ⊗ₜ[R] d) ⊗ₜ[R] m)).trans
          (tensorAssocContinuousLinearEquiv_tmul R C D M c d m)
  calc
    _ = b c d m := hflat
    _ = tensorLiftCLM R (C := C) (M := tensorLeftObj R D M) (N := N)
        ((tensorHomLinearEquiv R D M N).symm.toLinearMap.comp b)
        (show tensorLeftObj R C (tensorLeftObj R D M) from
          c ⊗ₜ[R] (d ⊗ₜ[R] m)) := hnested.symm
    _ = tensorLiftCLM R (C := C) (M := tensorLeftObj R D M) (N := N)
        ((tensorHomLinearEquiv R D M N).symm.toLinearMap.comp b)
        ((tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (c ⊗ₜ[R] d) ⊗ₜ[R] m)) :=
      congrArg (tensorLiftCLM R (C := C) (M := tensorLeftObj R D M) (N := N)
        ((tensorHomLinearEquiv R D M N).symm.toLinearMap.comp b)) hassoc.symm
    _ = _ := (ContinuousLinearMap.comp_apply
      (tensorLiftCLM R (C := C) (M := tensorLeftObj R D M) (N := N)
        ((tensorHomLinearEquiv R D M N).symm.toLinearMap.comp b))
      (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap
      (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
        (c ⊗ₜ[R] d) ⊗ₜ[R] m)).symm

/-- Currying after tensor reassociation is the algebraic lift of the twice-curried
family, with continuity retained in the right argument. -/
theorem tensorCurry_comp_tensorAssoc
    (R : Type uR) [CommRing R] [TopologicalSpace R]
    (C : ModuleCat.{uC} R) (D : ModuleCat.{uD} R)
    (M : TopModuleCat.{uM} R) (N : TopModuleCat.{uN} R)
    (f : tensorLeftObj R C (tensorLeftObj R D M) →L[R] N) :
    (tensorCurry R
      (C := ModuleCat.of R (C ⊗[R] D)) (M := M) (N := N)
      (f.comp (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap) :
        ModuleCat.of R (C ⊗[R] D) →ₗ[R] (M →L[R] N)) =
      TensorProduct.lift
        ((tensorHomLinearEquiv R D M N).toLinearMap.comp
          (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f)) := by
  apply TensorProduct.ext'
  intro c d
  apply ContinuousLinearMap.ext
  intro m
  have hfamily :
      ((tensorHomLinearEquiv R D M N).toLinearMap.comp
        (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f)) c =
      tensorHomLinearEquiv R D M N
        (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f c) :=
    (LinearMap.comp_apply (tensorHomLinearEquiv R D M N).toLinearMap
      (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f) c).trans
        (congrFun (LinearEquiv.coe_toLinearMap (tensorHomLinearEquiv R D M N))
          (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f c))
  calc
    _ = (f.comp (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap)
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (c ⊗ₜ[R] d) ⊗ₜ[R] m) :=
      tensorCurry_apply_apply R
        (C := ModuleCat.of R (C ⊗[R] D)) (M := M) (N := N)
        (f.comp (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap)
        (c ⊗ₜ[R] d) m
    _ = f ((tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (c ⊗ₜ[R] d) ⊗ₜ[R] m)) :=
      ContinuousLinearMap.comp_apply f
        (tensorAssocContinuousLinearEquiv R C D M).toContinuousLinearMap
        (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
          (c ⊗ₜ[R] d) ⊗ₜ[R] m)
    _ = f (show tensorLeftObj R C (tensorLeftObj R D M) from
        c ⊗ₜ[R] (d ⊗ₜ[R] m)) :=
      congrArg f
        ((ContinuousLinearEquiv.coe_apply (tensorAssocContinuousLinearEquiv R C D M)
          (show tensorLeftObj R (ModuleCat.of R (C ⊗[R] D)) M from
            (c ⊗ₜ[R] d) ⊗ₜ[R] m)).trans
              (tensorAssocContinuousLinearEquiv_tmul R C D M c d m))
    _ = tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f c
        (show tensorLeftObj R D M from d ⊗ₜ[R] m) :=
      (tensorCurry_apply_apply R (C := C) (M := tensorLeftObj R D M) (N := N)
        f c (show tensorLeftObj R D M from d ⊗ₜ[R] m)).symm
    _ = tensorHomLinearEquiv R D M N
        (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f c) d m :=
      (tensorHomLinearEquiv_apply_apply R (C := D) (M := M) (N := N)
        (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f c) d m).symm
    _ = ((tensorHomLinearEquiv R D M N).toLinearMap.comp
        (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f)) c d m :=
      congrArg (fun k : D →ₗ[R] (M →L[R] N) ↦ k d m) hfamily.symm
    _ = (TensorProduct.lift
        ((tensorHomLinearEquiv R D M N).toLinearMap.comp
          (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f)))
        (c ⊗ₜ[R] d) m :=
      congrArg (fun k : M →L[R] N ↦ k m)
        (TensorProduct.lift.tmul
          (f' := (tensorHomLinearEquiv R D M N).toLinearMap.comp
            (tensorCurry R (C := C) (M := tensorLeftObj R D M) (N := N) f)) c d).symm

end LiftCurry

end TopModuleCat
