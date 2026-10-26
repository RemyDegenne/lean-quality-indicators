/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import SimplicialObjects.TensorCoefficientMaps
public import Mathlib.Algebra.Homology.ShortComplex.Basic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.HomologicalComplexAbelian

/-!
# Short complexes from changes of normalized tensor coefficients

An exact pair of additive coefficient homomorphisms gives a short complex on the
original normalized tensor chain complexes. The coefficient universes `a`, `b`,
`c`, simplex universe `w` and padding universe `p` are independent. The common
category is `ModuleCat.{max a b c w p} ℤ`, using the balanced padding of coefficient
composition. Neither the carriers nor their canonical integer module structures
nor the alternating differentials are changed.

The field and component equations below identify this object without unfolding
its construction. All other record operations, including the zero-composite
identity and morphisms of short complexes, are those of Mathlib's `ShortComplex`.
No endpoint property is required to construct it. Injective and surjective
coefficient homomorphisms induce monomorphisms and epimorphisms of the original
chain complexes. A short exact coefficient pair gives a short exact sequence of
these complexes, by degreewise exactness in Mathlib's abelian-category API.

## References

* Mathlib's `CategoryTheory.ShortComplex`, its record API and degreewise
  short exactness for homological complexes, by Joël Riou.
* Mathlib's module-category monomorphism and epimorphism criteria, by Kim Morrison.
* The tensor coefficient maps and their composition and component equations in
  `SimplicialObjects.TensorCoefficientMaps`, by Formal Frontier Agents.
* May, *A Concise Course in Algebraic Topology*, revised edition, §16.1, for the
  normalized presentation motivating the tensor chain complexes.
-/

@[expose] public section

universe a b c w p

open CategoryTheory

namespace SSet

variable {A : Type a} {B : Type b} {C : Type c}
  [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]

/-- The short complex of normalized tensor chains associated to an exact coefficient
pair. Its zero composite follows from coefficient exactness and the composition
and zero formulas for the original chain coefficient maps. -/
noncomputable def tensorNormalizedChainComplexCoefficientShortComplex
    (g : A →+ B) (h : B →+ C) (hExact : Function.Exact g h) (S : SSet.{w}) :
    ShortComplex (ChainComplex (ModuleCat.{max a b c w p} ℤ) ℕ) where
  X₁ := tensorNormalizedChainComplex.{a, w, max b (max c p)} A S
  X₂ := tensorNormalizedChainComplex.{b, w, max a (max c p)} B S
  X₃ := tensorNormalizedChainComplex.{c, w, max b (max a p)} C S
  f := tensorNormalizedChainComplexCoefficientMap.{a, b, w, max c p} g S
  g := tensorNormalizedChainComplexCoefficientMap.{b, c, w, max a p} h S
  zero := by
    rw [← tensorNormalizedChainComplexCoefficientMap_comp.{a, b, c, w, p}]
    have hcomp : h.comp g = 0 := by
      ext x
      exact hExact.apply_apply_eq_zero x
    rw [hcomp, tensorNormalizedChainComplexCoefficientMap_zero]

/-- The left chain complex retains the original carrier and differential. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientShortComplex_X₁
    (g : A →+ B) (h : B →+ C) (hExact : Function.Exact g h) (S : SSet.{w}) :
    (tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
      g h hExact S).X₁ = tensorNormalizedChainComplex.{a, w, max b (max c p)} A S := rfl

/-- The middle chain complex retains the original carrier and differential. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientShortComplex_X₂
    (g : A →+ B) (h : B →+ C) (hExact : Function.Exact g h) (S : SSet.{w}) :
    (tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
      g h hExact S).X₂ = tensorNormalizedChainComplex.{b, w, max a (max c p)} B S := rfl

/-- The right chain complex retains the original carrier and differential. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientShortComplex_X₃
    (g : A →+ B) (h : B →+ C) (hExact : Function.Exact g h) (S : SSet.{w}) :
    (tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
      g h hExact S).X₃ = tensorNormalizedChainComplex.{c, w, max b (max a p)} C S := rfl

/-- The first arrow is the original chain coefficient map with common padding. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientShortComplex_f
    (g : A →+ B) (h : B →+ C) (hExact : Function.Exact g h) (S : SSet.{w}) :
    (tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
      g h hExact S).f =
        tensorNormalizedChainComplexCoefficientMap.{a, b, w, max c p} g S := rfl

/-- The second arrow is the original chain coefficient map with common padding. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientShortComplex_g
    (g : A →+ B) (h : B →+ C) (hExact : Function.Exact g h) (S : SSet.{w}) :
    (tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
      g h hExact S).g =
        tensorNormalizedChainComplexCoefficientMap.{b, c, w, max a p} h S := rfl

/-- Every component of the first arrow is the original raw tensor coefficient map. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientShortComplex_f_f
    (g : A →+ B) (h : B →+ C) (hExact : Function.Exact g h) (S : SSet.{w}) (n : ℕ) :
    ((tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
      g h hExact S).f).f n =
        tensorNormalizedCoefficientMap.{a, b, w, max c p} g S n := by
  rw [tensorNormalizedChainComplexCoefficientShortComplex_f,
    tensorNormalizedChainComplexCoefficientMap_f]

/-- Every component of the second arrow is the original raw tensor coefficient map. -/
@[simp]
theorem tensorNormalizedChainComplexCoefficientShortComplex_g_f
    (g : A →+ B) (h : B →+ C) (hExact : Function.Exact g h) (S : SSet.{w}) (n : ℕ) :
    ((tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
      g h hExact S).g).f n =
        tensorNormalizedCoefficientMap.{b, c, w, max a p} h S n := by
  rw [tensorNormalizedChainComplexCoefficientShortComplex_g,
    tensorNormalizedChainComplexCoefficientMap_f]

/-! ## Endpoint preservation and short exactness -/

/-- An injective coefficient homomorphism induces a monomorphism on the original
normalized tensor chain complexes. -/
theorem tensorNormalizedChainComplexCoefficientMap_mono (g : A →+ B)
    (hInj : Function.Injective g) (S : SSet.{w}) :
    Mono (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S) := by
  apply HomologicalComplex.mono_of_mono_f
  intro n
  rw [tensorNormalizedChainComplexCoefficientMap_f]
  exact (ModuleCat.mono_iff_injective _).2
    (tensorNormalizedCoefficientMap_injective.{a, b, w, p} g hInj S n)

/-- A surjective coefficient homomorphism induces an epimorphism on the original
normalized tensor chain complexes. -/
theorem tensorNormalizedChainComplexCoefficientMap_epi (g : A →+ B)
    (hSurj : Function.Surjective g) (S : SSet.{w}) :
    Epi (tensorNormalizedChainComplexCoefficientMap.{a, b, w, p} g S) := by
  apply HomologicalComplex.epi_of_epi_f
  intro n
  rw [tensorNormalizedChainComplexCoefficientMap_f]
  exact (ModuleCat.epi_iff_surjective _).2
    (tensorNormalizedCoefficientMap_surjective.{a, b, w, p} g hSurj S n)

/-- A coefficient pair with injective first map, exact middle and surjective second
map gives a short exact sequence on the original tensor chain complexes in
`ModuleCat.{max a b c w p} ℤ`. -/
theorem tensorNormalizedChainComplexCoefficientShortComplex_shortExact
    (g : A →+ B) (h : B →+ C) (hInj : Function.Injective g)
    (hExact : Function.Exact g h) (hSurj : Function.Surjective h) (S : SSet.{w}) :
    (tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
      g h hExact S).ShortExact := by
  apply HomologicalComplex.shortExact_of_degreewise_shortExact
  intro n
  refine { exact := ?_, mono_f := ?_, epi_g := ?_ }
  · apply (ShortComplex.moduleCat_exact_iff _).2
    have hf :
        (HomologicalComplex.eval (ModuleCat.{max a b c w p} ℤ)
          (ComplexShape.down ℕ) n).map
            (tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
              g h hExact S).f =
          tensorNormalizedCoefficientMap.{a, b, w, max c p} g S n := by
      rw [HomologicalComplex.eval_map,
        tensorNormalizedChainComplexCoefficientShortComplex_f_f]
    have hg :
        (HomologicalComplex.eval (ModuleCat.{max a b c w p} ℤ)
          (ComplexShape.down ℕ) n).map
            (tensorNormalizedChainComplexCoefficientShortComplex.{a, b, c, w, p}
              g h hExact S).g =
          tensorNormalizedCoefficientMap.{b, c, w, max a p} h S n := by
      rw [HomologicalComplex.eval_map,
        tensorNormalizedChainComplexCoefficientShortComplex_g_f]
    intro x hx
    rw [ShortComplex.map_g, hg] at hx
    rw [ShortComplex.map_f, hf]
    exact (tensorNormalizedCoefficientMap_exact.{a, b, c, w, p} g h hExact S n x).mp hx
  · rw [ShortComplex.map_f, HomologicalComplex.eval_map,
      tensorNormalizedChainComplexCoefficientShortComplex_f_f]
    exact (ModuleCat.mono_iff_injective _).2
      (tensorNormalizedCoefficientMap_injective.{a, b, w, max c p} g hInj S n)
  · rw [ShortComplex.map_g, HomologicalComplex.eval_map,
      tensorNormalizedChainComplexCoefficientShortComplex_g_f]
    exact (ModuleCat.epi_iff_surjective _).2
      (tensorNormalizedCoefficientMap_surjective.{b, c, w, max a p} h hSurj S n)

end SSet
