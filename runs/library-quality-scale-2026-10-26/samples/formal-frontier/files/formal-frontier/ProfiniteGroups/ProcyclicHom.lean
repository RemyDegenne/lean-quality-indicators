/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ProfiniteGroups.ProcyclicInvariant

/-!
# Continuous maps out of a procyclic profinite group

A prescribed value on a topological generator determines at most one continuous
homomorphism. It determines one precisely when the kernel exponents of the
associated common-source map are bounded by the exponents of the source. The target
need not be procyclic, and the prescribed value need not generate the target.

Surjectivity of the resulting map is an additional generator condition on the
image. The exponent inequality is not a criterion for mere existence of an
unspecified homomorphism to an arbitrary target.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §7, before Proposition
  (1.7.7) (topological-generator context; these homomorphism refinements are not attributed
  as printed results).
- Mathlib, `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Completion` (extension from a
  dense cyclic subgroup); `ProcyclicInvariant` supplies the quotient description.
-/

@[expose] public section

open Function

universe u v w

namespace ProfiniteGrp

/-- Continuous homomorphisms out of a procyclic group agree if they agree on a
supplied topological generator. -/
theorem continuousHom_ext_of_generator {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    {g : G} (hg : IsTopologicalGenerator G g) (f k : G →ₜ* H)
    (h : f g = k g) : f = k := by
  apply ContinuousMonoidHom.ext
  intro x
  obtain ⟨a, rfl⟩ := primewisePadicBaseMapOfGenerator_surjective G g hg x
  calc
    f (primewisePadicBaseMapOfGenerator G g a) =
        primewisePadicBaseMapOfGenerator H (f g) a :=
      congrArg (fun map : primewisePadic.{0} →ₜ* H ↦ map a)
        (primewisePadicBaseMapOfGenerator_naturality G H f g)
    _ = primewisePadicBaseMapOfGenerator H (k g) a := by rw [h]
    _ = k (primewisePadicBaseMapOfGenerator G g a) :=
      (congrArg (fun map : primewisePadic.{0} →ₜ* H ↦ map a)
        (primewisePadicBaseMapOfGenerator_naturality G H k g)).symm

/-- A continuous surjection from a compact group factors any continuous
homomorphism whose kernel contains its kernel, continuously and uniquely. -/
noncomputable def continuousHomLiftOfSurjective
    {A : ProfiniteGrp.{w}} {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (q : A →ₜ* G) (r : A →ₜ* H) (hq : Surjective q)
    (hker : q.toMonoidHom.ker ≤ r.toMonoidHom.ker) : G →ₜ* H := by
  let f : G →* H := q.toMonoidHom.liftOfSurjective hq ⟨r.toMonoidHom, hker⟩
  have hcomp : f.comp q.toMonoidHom = r.toMonoidHom := by
    exact q.toMonoidHom.liftOfRightInverse_comp (Function.surjInv hq)
      (Function.rightInverse_surjInv hq) ⟨r.toMonoidHom, hker⟩
  exact {
    f with
    continuous_toFun :=
      (Topology.IsQuotientMap.of_surjective_continuous hq q.continuous_toFun).continuous_iff.mpr
        (by
          convert r.continuous_toFun using 1
          funext a
          exact congrArg (fun map : A →* H ↦ map a) hcomp)
  }

/-- The quotient-map lift commutes with its surjective input. The kernel
inclusion is the condition that makes the descended map well-defined. -/
@[simp]
theorem continuousHomLiftOfSurjective_comp
    {A : ProfiniteGrp.{w}} {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (q : A →ₜ* G) (r : A →ₜ* H) (hq : Surjective q)
    (hker : q.toMonoidHom.ker ≤ r.toMonoidHom.ker) :
    (continuousHomLiftOfSurjective q r hq hker).comp q = r := by
  apply ContinuousMonoidHom.ext
  intro x
  change (q.toMonoidHom.liftOfSurjective hq ⟨r.toMonoidHom, hker⟩)
    (q x) = r x
  exact congrArg (fun map : A →* H ↦ map x)
    (q.toMonoidHom.liftOfRightInverse_comp (Function.surjInv hq)
      (Function.rightInverse_surjInv hq) ⟨r.toMonoidHom, hker⟩)

/-- Inclusion of the kernels of common-source maps is precisely reversed
pointwise comparison of their primewise kernel exponents. -/
theorem baseMap_kernel_le_iff {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (g : G) (h : H) :
    (primewisePadicBaseMapOfGenerator G g).toMonoidHom.ker ≤
        (primewisePadicBaseMapOfGenerator H h).toMonoidHom.ker ↔
      ∀ p, primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator H h) p ≤
        primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G g) p := by
  let q := primewisePadicBaseMapOfGenerator G g
  let r := primewisePadicBaseMapOfGenerator H h
  have key : q.toMonoidHom.ker ≤ r.toMonoidHom.ker ↔
      primewisePadicKernelIdeal q ≤ primewisePadicKernelIdeal r := by
    constructor
    · intro hker x hx
      apply (mem_primewisePadicKernelIdeal r x).mpr
      apply hker
      exact (mem_primewisePadicKernelIdeal q x).mp hx
    · intro hideal x hx
      let a : primewisePadicRing.{0} :=
        (primewisePadicRingMultiplicativeEquiv.{0}.symm x).toAdd
      have ha : a ∈ primewisePadicKernelIdeal q :=
        (mem_primewisePadicKernelIdeal q a).mpr (by simpa [a] using hx)
      have hb := (mem_primewisePadicKernelIdeal r a).mp (hideal ha)
      simpa [a] using hb
  change q.toMonoidHom.ker ≤ r.toMonoidHom.ker ↔ _
  rw [key, primewisePadicKernelIdeal_eq_idealOfExponents,
    primewisePadicKernelIdeal_eq_idealOfExponents]
  exact primewisePadicIdealOfExponents_le_iff

/-- The generator-independent exponent condition for mapping `g` to `h`.
It makes no generation assumption about the target. -/
theorem baseMap_kernel_le_iff_exponents {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H) :
    (primewisePadicBaseMapOfGenerator G g).toMonoidHom.ker ≤
        (primewisePadicBaseMapOfGenerator H h).toMonoidHom.ker ↔
      ∀ p, primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator H h) p ≤
        hG.exponents p := by
  simpa only [hG.exponents_eq_baseMap_of_generator g hg] using
    (baseMap_kernel_le_iff g h)

/-- The canonical continuous homomorphism with prescribed value on `g`.
The required inequality is a genuine existence condition, not a condition for
mere existence of some homomorphism. -/
noncomputable def factorOfGenerator {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H)
    (hadmissible : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p) : G →ₜ* H :=
  continuousHomLiftOfSurjective
    (primewisePadicBaseMapOfGenerator G g)
    (primewisePadicBaseMapOfGenerator H h)
    (primewisePadicBaseMapOfGenerator_surjective G g hg)
    ((baseMap_kernel_le_iff_exponents hG g hg h).mpr hadmissible)

/-- The factor prescribed by an image of the generator commutes with both
primewise common-source maps. -/
@[simp]
theorem factorOfGenerator_comp_baseMap {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H)
    (hadmissible : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p) :
    (factorOfGenerator hG g hg h hadmissible).comp
      (primewisePadicBaseMapOfGenerator G g) =
        primewisePadicBaseMapOfGenerator H h :=
  continuousHomLiftOfSurjective_comp _ _ _ _

/-- The descended factor really takes the supplied source generator to its
prescribed value in the possibly nonprocyclic target. -/
@[simp]
theorem factorOfGenerator_apply_generator {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H)
    (hadmissible : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p) :
    factorOfGenerator hG g hg h hadmissible g = h := by
  have heq := congrArg (fun map : primewisePadic.{0} →ₜ* H ↦
    map (primewisePadicDiagonal.{0} 1))
    (factorOfGenerator_comp_baseMap hG g hg h hadmissible)
  change (factorOfGenerator hG g hg h hadmissible)
    (primewisePadicBaseMapOfGenerator G g (primewisePadicDiagonal 1)) =
      primewisePadicBaseMapOfGenerator H h (primewisePadicDiagonal 1) at heq
  simpa only [primewisePadicBaseMapOfGenerator_diagonal, zpow_one] using heq

/-- Evaluation at a generator has a unique prescribed inverse value exactly
when the common-source kernel exponents satisfy the pointwise condition. -/
theorem existsUnique_continuousHom_apply_generator_iff
    {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H) :
    (∃! f : G →ₜ* H, f g = h) ↔
      ∀ p, primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator H h) p ≤
        hG.exponents p := by
  constructor
  · rintro ⟨f, hf, -⟩
    apply (baseMap_kernel_le_iff_exponents hG g hg h).mp
    intro x hx
    have heq : f.comp (primewisePadicBaseMapOfGenerator G g) =
        primewisePadicBaseMapOfGenerator H h := by
      simpa only [hf] using primewisePadicBaseMapOfGenerator_naturality G H f g
    change (primewisePadicBaseMapOfGenerator H h) x = 1
    rw [← congrArg (fun map : primewisePadic.{0} →ₜ* H ↦ map x) heq]
    change f (primewisePadicBaseMapOfGenerator G g x) = 1
    rw [show primewisePadicBaseMapOfGenerator G g x = 1 from hx]
    exact map_one f
  · intro hadmissible
    refine ⟨factorOfGenerator hG g hg h hadmissible,
      factorOfGenerator_apply_generator hG g hg h hadmissible, ?_⟩
    intro f hf
    exact continuousHom_ext_of_generator hg _ _ (hf.trans
      (factorOfGenerator_apply_generator hG g hg h hadmissible).symm)

/-- The canonical factor is onto exactly when its prescribed image generates
the entire target. -/
theorem factorOfGenerator_surjective_iff {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) (h : H)
    (hadmissible : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p) :
    Surjective (factorOfGenerator hG g hg h hadmissible) ↔
      IsTopologicalGenerator H h := by
  constructor
  · intro hf
    simpa only [factorOfGenerator_apply_generator] using
      hg.map (factorOfGenerator hG g hg h hadmissible) hf
  · intro hh
    have hsurj : Surjective (primewisePadicBaseMapOfGenerator H h) :=
      primewisePadicBaseMapOfGenerator_surjective H h hh
    rw [← factorOfGenerator_comp_baseMap hG g hg h hadmissible] at hsurj
    exact Function.Surjective.of_comp (show Surjective
      ((factorOfGenerator hG g hg h hadmissible : G →ₜ* H) ∘
        primewisePadicBaseMapOfGenerator G g) from hsurj)

/-- A continuous quotient between procyclic profinite groups exists exactly
when the exponents of the target are bounded by those of the source.

The quotient classification in Neukirch–Schmidt–Wingberg, *Cohomology of Number
Fields*, Ch. I §7, before Proposition (1.7.7) motivates this order criterion; the
homomorphism-level refinement is proved here using Mathlib’s profinite completion. -/
theorem exists_surjective_continuousHom_iff_exponents_le
    {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (hH : IsProcyclic H) :
    (∃ f : G →ₜ* H, Surjective f) ↔ ∀ p, hH.exponents p ≤ hG.exponents p := by
  constructor
  · rintro ⟨f, hf⟩
    let g : G := hG.choose
    have hg : IsTopologicalGenerator G g := hG.choose_spec
    have hh : IsTopologicalGenerator H (f g) := hg.map f hf
    have hmap := (existsUnique_continuousHom_apply_generator_iff hG g hg (f g)).mp
      ⟨f, rfl, fun k hk ↦ continuousHom_ext_of_generator hg _ _ hk⟩
    simpa only [hH.exponents_eq_baseMap_of_generator (f g) hh] using hmap
  · intro hle
    let g : G := hG.choose
    let h : H := hH.choose
    have hg : IsTopologicalGenerator G g := hG.choose_spec
    have hh : IsTopologicalGenerator H h := hH.choose_spec
    have hadmissible : ∀ p, primewisePadicKernelExponents
        (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p := by
      simpa only [← hH.exponents_eq_baseMap_of_generator h hh] using hle
    exact ⟨factorOfGenerator hG g hg h hadmissible,
      (factorOfGenerator_surjective_iff hG g hg h hadmissible).mpr hh⟩

/-- The factor assigning the source generator to itself is the identity. -/
theorem factorOfGenerator_self {G : ProfiniteGrp.{u}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g)
    (hadmissible : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator G g) p ≤ hG.exponents p) :
    factorOfGenerator hG g hg g hadmissible = ContinuousMonoidHom.id G := by
  exact continuousHom_ext_of_generator hg _ _ (by simp)

/-- The identity element is always an admissible image of a generator. -/
theorem one_admissible {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) :
    ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H 1) p ≤ hG.exponents p := by
  apply (existsUnique_continuousHom_apply_generator_iff hG g hg 1).mp
  refine ⟨1, by simp, ?_⟩
  intro f hf
  exact continuousHom_ext_of_generator hg _ _ (by simpa using hf)

/-- Sending a topological generator to the identity gives the trivial map. -/
theorem factorOfGenerator_one {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    (hG : IsProcyclic G) (g : G) (hg : IsTopologicalGenerator G g) :
    factorOfGenerator hG g hg (1 : H) (one_admissible hG g hg) = 1 := by
  exact continuousHom_ext_of_generator hg _ _ (by simp)

/-- Composing two canonical factors agrees with evaluation at the source
generator, whenever the resulting prescribed image is admissible. -/
theorem factorOfGenerator_comp {G : ProfiniteGrp.{u}} {H : ProfiniteGrp.{v}}
    {K : ProfiniteGrp.{w}} (hG : IsProcyclic G) (g : G)
    (hg : IsTopologicalGenerator G g) (hH : IsProcyclic H)
    (h : H) (hh : IsTopologicalGenerator H h) (k : K)
    (ha : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator H h) p ≤ hG.exponents p)
    (hb : ∀ p, primewisePadicKernelExponents
      (primewisePadicBaseMapOfGenerator K k) p ≤ hH.exponents p) :
    (factorOfGenerator hH h hh k hb).comp
        (factorOfGenerator hG g hg h ha) =
      factorOfGenerator hG g hg k (fun p ↦
        (hb p).trans (by simpa only [hH.exponents_eq_baseMap_of_generator h hh] using ha p)) := by
  apply continuousHom_ext_of_generator hg
  simp

end ProfiniteGrp
