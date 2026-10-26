/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import AlgebraicDirectLimits.Topology.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import Mathlib.RingTheory.Flat.Basic

/-!
# Tensor functor with fixed algebraic coefficients

For a fixed algebraic module `C`, `TopModuleCat.tensorLeftFunctor R C` sends a
variable topological module `M` to `TopModuleCat.tensorLeftObj R C M`. Its map is
`TopModuleCat.tensorMapCLM` with the identity on `C` and the given continuous
linear map on the right. Thus the tensor carrier, scalar action and one-sided
topology are those of `tensorLeftObj`, without a topology on `C`.

The functor is additive. The characteristic lemmas describe its object, its
continuous map, its underlying algebraic tensor map and its pure-tensor values;
identity, composition, zero and addition use the standard `Functor` API.

The scalar and two carrier universes are independent: a coefficient module in
universe `uC` and an input in universe `uM` give an output in `max uC uM`.
The commutative scalar ring needs only a supplied topology, and the bundled
topological modules supply jointly continuous actions. No finiteness, freeness
or separation hypothesis is required.

When `C` is flat over `R`, tensoring preserves injectivity of the underlying
continuous linear maps and hence categorical monomorphisms. The latter uses the
forgetful functor to algebraic modules, which is a right adjoint. These are not
claims about topological embeddings, closed ranges or strict exactness.

## References

This construction reuses Formal Frontier Agents' one-sided tensor and continuous
tensor maps, including the coinduced topology and tensor models.
The coefficient tensor construction supplies the categorical bundling pattern
in the other variable. Mathlib's topological-module category is due to Richard
Hill and Andrew Yang, its algebraic-module interface to Robert A. Spencer and
Markus Himmel, its tensor-map API to Kenny Lau and Mario Carneiro, and its
additive-functor API to Adam Topaz and Kim Morrison. Formal Frontier Agents contributed the
fixed-coefficient functor and its additive interface. The flat-coefficient
argument reuses Mathlib's flat-module API by Johan Commelin, Jujian Zhang and
Yongle Hu, right-adjoint limit preservation by Reid Barton and Johan Commelin,
pullback preservation of monomorphisms by Bhavik Mehta, and the module
monomorphism criterion by Kim Morrison.
-/

@[expose] public section

open CategoryTheory
open scoped TensorProduct

universe uR uC uM

namespace TopModuleCat

variable (R : Type uR) [CommRing R] [TopologicalSpace R]
variable (C : ModuleCat.{uC} R)

/-- Tensor with fixed algebraic coefficients, covariantly in the topological right
factor. The objects retain the one-sided tensor topology and canonical scalar action. -/
noncomputable def tensorLeftFunctor :
    TopModuleCat.{uM} R ⥤ TopModuleCat.{max uC uM} R where
  obj M := tensorLeftObj R C M
  map {M N} g := CategoryTheory.ConcreteCategory.ofHom
    (C := TopModuleCat.{max uC uM} R)
    (X := tensorLeftObj R C M) (Y := tensorLeftObj R C N)
    (tensorMapCLM R (LinearMap.id : C →ₗ[R] C) g.hom)
  map_id M := by
    apply ConcreteCategory.ext
    simpa only [ConcreteCategory.hom_ofHom, TopModuleCat.hom_id] using
      (tensorMapCLM_id R (C := C) (M := M))
  map_comp {M N P} g h := by
    apply ConcreteCategory.ext
    simpa only [ConcreteCategory.hom_ofHom, TopModuleCat.hom_comp,
      LinearMap.id_comp] using
      (tensorMapCLM_comp R (LinearMap.id : C →ₗ[R] C)
        (LinearMap.id : C →ₗ[R] C) g.hom h.hom)

/-- The tensor functor's object is the one-sided topological tensor. -/
@[simp]
theorem tensorLeftFunctor_obj (M : TopModuleCat.{uM} R) :
    (tensorLeftFunctor R C).obj M = tensorLeftObj R C M := rfl

/-- The tensor functor acts by the continuous tensor map with coefficient identity. -/
@[simp]
theorem tensorLeftFunctor_map_hom {M N : TopModuleCat.{uM} R} (g : M ⟶ N) :
    ((tensorLeftFunctor R C).map g).hom =
      tensorMapCLM R (LinearMap.id : C →ₗ[R] C) g.hom :=
  CategoryTheory.ConcreteCategory.hom_ofHom
    (C := TopModuleCat.{max uC uM} R)
    (X := tensorLeftObj R C M) (Y := tensorLeftObj R C N)
    (tensorMapCLM R (LinearMap.id : C →ₗ[R] C) g.hom)

/-- Forgetting continuity of a functor map gives Mathlib's algebraic tensor map. -/
@[simp]
theorem tensorLeftFunctor_map_toLinearMap {M N : TopModuleCat.{uM} R} (g : M ⟶ N) :
    ((tensorLeftFunctor R C).map g).hom.toLinearMap =
      TensorProduct.map (LinearMap.id : C →ₗ[R] C) g.hom.toLinearMap :=
  tensorMapCLM_toLinearMap R (LinearMap.id : C →ₗ[R] C) g.hom

/-- A functor map leaves the coefficient of each pure tensor unchanged. -/
@[simp]
theorem tensorLeftFunctor_map_tmul {M N : TopModuleCat.{uM} R} (g : M ⟶ N)
    (c : C) (m : M) :
    ((tensorLeftFunctor R C).map g).hom (c ⊗ₜ[R] m) = c ⊗ₜ[R] g.hom m :=
  tensorMapCLM_tmul R (LinearMap.id : C →ₗ[R] C) g.hom c m

/-- Tensoring with fixed algebraic coefficients is an additive functor. -/
instance tensorLeftFunctor_additive :
    (tensorLeftFunctor R C :
      TopModuleCat.{uM} R ⥤ TopModuleCat.{max uC uM} R).Additive where
  map_add {M N g h} := by
    apply ConcreteCategory.ext
    exact tensorMapCLM_add_right R (LinearMap.id : C →ₗ[R] C) g.hom h.hom

/-- With flat coefficients, an injective continuous linear map induces an injective
map on the one-sided tensors. This is Mathlib's flat-module tensor injectivity. -/
theorem tensorLeftFunctor_map_injective [Module.Flat R C]
    {M N : TopModuleCat.{uM} R} (g : M ⟶ N) (hg : Function.Injective g.hom) :
    Function.Injective ((tensorLeftFunctor R C).map g).hom := by
  intro x y hxy
  apply Module.Flat.lTensor_preserves_injective_linearMap (M := C) g.hom.toLinearMap hg
  have hlTensor :
      g.hom.toLinearMap.lTensor C =
        TensorProduct.map (LinearMap.id : C →ₗ[R] C) g.hom.toLinearMap :=
    LinearMap.lTensor_def (M := C) (f := g.hom.toLinearMap)
  simp only [hlTensor]
  simp only [tensorLeftFunctor_map_hom] at hxy
  exact (tensorMapCLM_apply R (LinearMap.id : C →ₗ[R] C) g.hom x).symm.trans
    (hxy.trans (tensorMapCLM_apply R (LinearMap.id : C →ₗ[R] C) g.hom y))

/-- Tensoring with a flat algebraic coefficient module preserves monomorphisms. -/
instance tensorLeftFunctor_preservesMonomorphisms [Module.Flat R C] :
    (tensorLeftFunctor R C :
      TopModuleCat.{uM} R ⥤ TopModuleCat.{max uC uM} R).PreservesMonomorphisms where
  preserves {M N} g _ := by
    let U : TopModuleCat.{uM} R ⥤ ModuleCat.{uM} R := forget₂ _ _
    haveI : U.PreservesMonomorphisms :=
      CategoryTheory.preservesMonomorphisms_of_preservesLimitsOfShape U
    have hg : Function.Injective g.hom :=
      (ModuleCat.mono_iff_injective (U.map g)).mp (Functor.map_mono U g)
    exact ConcreteCategory.mono_of_injective _ (tensorLeftFunctor_map_injective R C g hg)

end TopModuleCat
