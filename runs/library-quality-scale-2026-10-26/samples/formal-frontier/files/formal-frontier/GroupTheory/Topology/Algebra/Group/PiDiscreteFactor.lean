/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import GroupTheory.Topology.Algebra.OpenSubgroup.Pi
public import Mathlib.Algebra.Group.Subgroup.Basic
public import Mathlib.GroupTheory.QuotientGroup.Basic
public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import Mathlib.Topology.Algebra.Group.Quotient
public import Mathlib.Topology.Order

/-!
# Finite-coordinate quotient factorization of continuous homomorphisms

A continuous group homomorphism from a dependent product to a discrete group
factors through quotients of finitely many coordinates by open normal subgroups.
The index, source factors and target have independent universes. Neither the index
nor the target is assumed finite. Compactness is needed only for the application
in which the selected coordinate quotients, and hence their product, are finite.

`ContinuousMonoidHom.piQuotient` is coordinate restriction followed by the
canonical group quotient maps for any selected family of normal subgroups;
openness is not needed for this construction. Its kernel is the cylinder
imposing the selected normal subgroups, and it is surjective. The factorization
equation is an equality of the existing bundled continuous homomorphisms, not
merely of their underlying continuous maps. The descended homomorphism need not
be injective.

## Implementation notes

No continuity of the source group operations is assumed. The selected subgroups
can be taken to be kernels of continuous coordinate homomorphisms to the discrete
target. Their quotients are discrete because the induced quotient homomorphisms
are continuous and injective. Mere openness of an arbitrary normal subgroup need
not make its quotient discrete without operation-continuity assumptions. The
universal-property API asks only that the selected projection be a quotient map;
intrinsic stage discreteness is one sufficient condition, since the projection
is continuous and surjective. Compactness of the factors makes the selected
discrete quotients finite. Without compactness, the selected discrete stage may
be infinite. No Hausdorffness, total disconnectedness or nonarchimedean
assumption is needed.

## References

- Formal Frontier Agents, finite-cylinder containment and the supported-part/tail
  decomposition in `OpenNormalSubgroup.exists_finset_pi_subset`.
- Monica Omar's finite-supported product-membership API in
  `Mathlib.Algebra.Group.Submonoid.Finite`, in particular
  `Submonoid.pi_mem_of_mulSingle_mem_aux`, which also applies to subgroups.
- Mathlib, `ContinuousMonoidHom`, `MonoidHom.pi`, `Pi.evalMonoidHom`,
  `QuotientGroup.mk'`, `QuotientGroup.kerLift`, `QuotientGroup.lift`,
  `QuotientGroup.quotientKerEquivOfSurjective`,
  `QuotientGroup.isQuotientMap_mk`, `QuotientGroup.kerLift_injective`,
  `Topology.IsQuotientMap.continuous_iff`, `IsOpenMap.isQuotientMap`,
  `DiscreteTopology.of_continuous_injective`, `Quotient.compactSpace`, and
  `finite_of_compact_of_discrete`.
-/

@[expose] public section

namespace ContinuousMonoidHom

universe uI uG uH

variable {I : Type uI} {G : I → Type uG}
  [∀ i, Group (G i)] [∀ i, TopologicalSpace (G i)]

/-- Restrict to a finite set of coordinates and quotient each selected factor
by its specified normal subgroup. Unselected coordinates are unrestricted;
openness and continuity of the group operations are not required. -/
def piQuotient (s : Finset I) (N : ∀ i : s, Subgroup (G i))
    [∀ i : s, (N i).Normal] : (∀ i, G i) →ₜ* (∀ i : s, G i ⧸ N i) where
  toMonoidHom := MonoidHom.pi fun i : s =>
    (QuotientGroup.mk' (N i)).comp (Pi.evalMonoidHom G (i : I))
  continuous_toFun := continuous_pi fun i =>
    QuotientGroup.continuous_mk.comp (continuous_apply (i : I))

@[simp]
theorem piQuotient_apply (s : Finset I) (N : ∀ i : s, Subgroup (G i))
    [∀ i : s, (N i).Normal] (x : ∀ i, G i) (i : s) :
    piQuotient s N x i = QuotientGroup.mk (x i) := rfl

/-- The kernel of the selected quotient projection is exactly its finite
cylinder; no condition is imposed on unselected coordinates. -/
@[simp]
theorem mem_ker_piQuotient (s : Finset I) (N : ∀ i : s, Subgroup (G i))
    [∀ i : s, (N i).Normal] (x : ∀ i, G i) :
    x ∈ (piQuotient s N).toMonoidHom.ker ↔ ∀ i : s, x i ∈ N i := by
  change piQuotient (G := G) s N x = 1 ↔ _
  constructor
  · intro hx i
    apply (QuotientGroup.eq_one_iff (N := N i) (x i)).mp
    simpa only [piQuotient_apply, Pi.one_apply] using congrFun hx i
  · intro hx
    funext i
    simpa only [piQuotient_apply, Pi.one_apply] using
      (QuotientGroup.eq_one_iff (N := N i) (x i)).mpr (hx i)

/-- Every tuple in the selected quotient product has a preimage in the full
product, including when the selected set is empty. -/
theorem piQuotient_surjective (s : Finset I)
    (N : ∀ i : s, Subgroup (G i)) [∀ i : s, (N i).Normal] :
    Function.Surjective (piQuotient s N) := by
  classical
  intro y
  let a : ∀ i : s, G i := fun i =>
    Function.surjInv (QuotientGroup.mk'_surjective (N i)) (y i)
  refine ⟨(fun i => if hi : i ∈ s then a ⟨i, hi⟩ else 1), ?_⟩
  funext i
  simp only [piQuotient_apply, dite_eq_left i.property]
  exact Function.surjInv_eq (QuotientGroup.mk'_surjective (N i)) (y i)

/-- If the selected projection is a quotient map, a continuous homomorphism
descends uniquely through it exactly when its kernel contains the projection's
cylinder. No openness, quotient discreteness or continuity of source
multiplication is required. Algebraic descent to a monoid uses Mathlib's
`QuotientGroup.lift` and `QuotientGroup.quotientKerEquivOfSurjective`;
`Topology.IsQuotientMap.continuous_iff` supplies continuity. -/
theorem piQuotient_existsUnique_factor
    (s : Finset I) (N : ∀ i : s, Subgroup (G i)) [∀ i : s, (N i).Normal]
    (hq : Topology.IsQuotientMap (piQuotient s N))
    {H : Type uH} [Monoid H] [TopologicalSpace H]
    (f : (∀ i, G i) →ₜ* H) :
    (∃! fbar : (∀ i : s, G i ⧸ N i) →ₜ* H,
      fbar.comp (piQuotient s N) = f) ↔
      (piQuotient s N).toMonoidHom.ker ≤ f.toMonoidHom.ker := by
  let q := piQuotient (G := G) s N
  change (∃! fbar : (∀ i : s, G i ⧸ N i) →ₜ* H, fbar.comp q = f) ↔
    q.toMonoidHom.ker ≤ f.toMonoidHom.ker
  constructor
  · rintro ⟨fbar, hfbar, _⟩ x hx
    apply MonoidHom.mem_ker.mpr
    have hxq : q x = 1 := MonoidHom.mem_ker.mp hx
    calc
      f x = fbar (q x) := (DFunLike.congr_fun hfbar x).symm
      _ = fbar 1 := congrArg fbar hxq
      _ = 1 := map_one fbar
  · intro hker
    let e : (∀ i, G i) ⧸ q.toMonoidHom.ker ≃* (∀ i : s, G i ⧸ N i) :=
      QuotientGroup.quotientKerEquivOfSurjective q.toMonoidHom hq.surjective
    let fLift := QuotientGroup.lift q.toMonoidHom.ker f.toMonoidHom hker
    let g : (∀ i : s, G i ⧸ N i) →* H := fLift.comp e.symm.toMonoidHom
    have hgq (x : ∀ i, G i) : g (q x) = f x := by
      have hex : e (QuotientGroup.mk x) = q x := rfl
      change fLift (e.symm (q x)) = f x
      rw [← hex, e.symm_apply_apply]
      exact QuotientGroup.lift_mk' q.toMonoidHom.ker hker x
    have hg_cont : Continuous g := by
      apply hq.continuous_iff.mpr
      have hgcomp : (g : (∀ i : s, G i ⧸ N i) → H) ∘ q =
          (f : (∀ i, G i) → H) := funext hgq
      rw [hgcomp]
      exact f.continuous_toFun
    let fbar : (∀ i : s, G i ⧸ N i) →ₜ* H :=
      { toMonoidHom := g, continuous_toFun := hg_cont }
    have hfbar : fbar.comp q = f := ContinuousMonoidHom.ext hgq
    refine ⟨fbar, hfbar, ?_⟩
    intro fbar' hfbar'
    apply ContinuousMonoidHom.ext
    intro y
    obtain ⟨x, rfl⟩ := hq.surjective y
    exact (DFunLike.congr_fun hfbar' x).trans (DFunLike.congr_fun hfbar x).symm

variable {H : Type uH} [Group H] [TopologicalSpace H] [DiscreteTopology H]

private theorem discreteTopology_quotient_ker
    {A : Type*} [Group A] [TopologicalSpace A] (g : A →ₜ* H) :
    DiscreteTopology (A ⧸ g.toMonoidHom.ker) := by
  have hc : Continuous (QuotientGroup.kerLift g.toMonoidHom) := by
    apply (QuotientGroup.isQuotientMap_mk g.toMonoidHom.ker).continuous_iff.mpr
    change Continuous
      (fun x : A => QuotientGroup.kerLift g.toMonoidHom (QuotientGroup.mk x))
    exact g.continuous_toFun.congr fun x =>
      (QuotientGroup.kerLift_mk g.toMonoidHom x).symm
  exact DiscreteTopology.of_continuous_injective hc
    (QuotientGroup.kerLift_injective g.toMonoidHom)

/-- A continuous group homomorphism from an arbitrary dependent product to a
discrete group factors through quotients of finitely many coordinates by open
normal subgroups with discrete quotients. Neither compactness nor continuity of
source multiplication is required. The selected discrete product may be infinite,
and the descended homomorphism need not be injective. -/
theorem exists_finset_openNormalSubgroup_pi_factor (f : (∀ i, G i) →ₜ* H) :
    ∃ (s : Finset I) (N : ∀ i : s, OpenNormalSubgroup (G i))
      (fbar : (∀ i : s, G i ⧸ (N i).toSubgroup) →ₜ* H),
      fbar.comp (piQuotient s (fun i => (N i).toSubgroup)) = f ∧
      (∀ i : s, DiscreteTopology (G i ⧸ (N i).toSubgroup)) ∧
      DiscreteTopology (∀ i : s, G i ⧸ (N i).toSubgroup) := by
  classical
  let M : OpenNormalSubgroup H :=
    { toOpenSubgroup :=
        { toSubgroup := ⊥
          isOpen' := isOpen_discrete _ }
      isNormal' := inferInstance }
  let K : OpenNormalSubgroup (∀ i, G i) :=
    { toOpenSubgroup := M.toOpenSubgroup.comap f.toMonoidHom f.continuous
      isNormal' := M.isNormal'.comap f.toMonoidHom }
  obtain ⟨s, N₀, hN₀⟩ := OpenNormalSubgroup.exists_finset_pi_subset K
  let axis : ∀ i, G i →ₜ* H := fun i =>
    { toMonoidHom := f.toMonoidHom.comp (MonoidHom.mulSingle G i)
      continuous_toFun := f.continuous.comp (continuous_mulSingle (A := G) i) }
  let N : ∀ i : s, OpenNormalSubgroup (G i) := fun i =>
    { toOpenSubgroup := M.toOpenSubgroup.comap (axis i).toMonoidHom (axis i).continuous
      isNormal' := M.isNormal'.comap (axis i).toMonoidHom }
  let : ∀ i : s, (N i).toSubgroup.Normal := fun i => (N i).isNormal'
  have hN : ∀ i : s, DiscreteTopology (G i ⧸ (N i).toSubgroup) := by
    intro i
    change DiscreteTopology (G i ⧸ (⊥ : Subgroup H).comap (axis i).toMonoidHom)
    rw [MonoidHom.comap_bot]
    exact discreteTopology_quotient_ker (axis i)
  let : ∀ i : s, DiscreteTopology (G i ⧸ (N i).toSubgroup) := hN
  have hStage : DiscreteTopology (∀ i : s, G i ⧸ (N i).toSubgroup) := inferInstance
  have hker : (piQuotient s (fun i => (N i).toSubgroup)).toMonoidHom.ker ≤
      f.toMonoidHom.ker := by
    intro x hx
    have hxN := (mem_ker_piQuotient s (fun i => (N i).toSubgroup) x).mp hx
    -- The exact axis kernels control the supported part.
    have ht : s.piecewise x 1 ∈ f.toMonoidHom.ker := by
      refine Submonoid.pi_mem_of_mulSingle_mem_aux s (s.piecewise x 1) ?_ ?_
      · intro i hi
        simp [hi]
      · intro i hi
        have hiM : Pi.mulSingle i (x i) ∈ f.toMonoidHom.ker := hxN ⟨i, hi⟩
        simpa only [Finset.piecewise_eq_of_mem s x 1 hi] using hiM
    -- Only the old finite cylinder is needed for the unrestricted tail.
    have hr : s.piecewise (1 : ∀ i, G i) x ∈ f.toMonoidHom.ker := by
      apply hN₀
      intro i
      rw [Finset.piecewise_eq_of_mem s (1 : ∀ i, G i) x i.property]
      exact one_mem (N₀ i)
    have hx_eq : x = s.piecewise x 1 * s.piecewise (1 : ∀ i, G i) x := by
      ext i
      by_cases hi : i ∈ s <;> simp [hi]
    rw [hx_eq]
    exact mul_mem ht hr
  have ho : IsOpenMap (piQuotient s (fun i => (N i).toSubgroup)) :=
    fun _ _ => isOpen_discrete _
  have hq : Topology.IsQuotientMap (piQuotient s (fun i => (N i).toSubgroup)) :=
    ho.isQuotientMap (map_continuous _) (piQuotient_surjective s (fun i => (N i).toSubgroup))
  obtain ⟨fbar, hfac, _⟩ :=
    (piQuotient_existsUnique_factor s (fun i => (N i).toSubgroup) hq f).mpr hker
  exact ⟨s, N, fbar, hfac, hN, hStage⟩

/-- If the factors are compact, the same finite-coordinate factorization has
finite coordinate quotients and a finite discrete quotient product. The discrete
target may still be infinite. This is the compact-group finite-stage application
of finite-coordinate factorization. -/
theorem exists_finset_openNormalSubgroup_pi_factor_finite
    [∀ i, CompactSpace (G i)] (f : (∀ i, G i) →ₜ* H) :
    ∃ (s : Finset I) (N : ∀ i : s, OpenNormalSubgroup (G i))
      (fbar : (∀ i : s, G i ⧸ (N i).toSubgroup) →ₜ* H),
      fbar.comp (piQuotient s (fun i => (N i).toSubgroup)) = f ∧
      (∀ i : s, Finite (G i ⧸ (N i).toSubgroup)) ∧
      Finite (∀ i : s, G i ⧸ (N i).toSubgroup) ∧
      DiscreteTopology (∀ i : s, G i ⧸ (N i).toSubgroup) := by
  obtain ⟨s, N, fbar, hfactor, hquot, hstage⟩ :=
    exists_finset_openNormalSubgroup_pi_factor (G := G) f
  let : ∀ i : s, DiscreteTopology (G i ⧸ (N i).toSubgroup) := hquot
  have hfinite : ∀ i : s, Finite (G i ⧸ (N i).toSubgroup) :=
    fun _ => finite_of_compact_of_discrete
  let : ∀ i : s, Finite (G i ⧸ (N i).toSubgroup) := hfinite
  exact ⟨s, N, fbar, hfactor, hfinite, inferInstance, hstage⟩

end ContinuousMonoidHom
