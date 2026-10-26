/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.PointwiseContinuousMap
public import Mathlib.Topology.Algebra.Group.Quotient

/-!
# Restricting twisted coinduction along a subgroup

A chosen **continuous** section of `G → G ⧸ H` identifies the restriction of
the twisted coinduction on `C(G, B)` with twisted coinduction on
`C(H, C(G ⧸ H, B))`. The `H`-action on the inner coefficient is pointwise,
not trivial, and `G ⧸ H` is only a space for a nonnormal subgroup.

The coordinates are `t ↦ (t * s(q(t⁻¹)), q(t⁻¹))` with inverse
`(h,c) ↦ h * (s c)⁻¹`. In particular the inversion in the quotient coordinate
cannot be discarded. The resulting isomorphism depends on the chosen section;
it does not assert a canonical or a multiplicative splitting. For the source's
closed-subgroup case, see `ProfiniteCoinducedRestriction`.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, I §3,
  Proposition 1.3.6(ii) and I §1, Exercise 4.
- Mathlib's twisted continuous coinduction and compact-open currying.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option warningAsError true

@[expose] public section

universe u v w

namespace TopRep

open CategoryTheory

variable {k : Type u} [Ring k] [TopologicalSpace k]
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (H : Subgroup G)

/-- The section-dependent equivalence of restricted twisted coinduction with
coinduction of the pointwise continuous-function representation. Neither
normality nor discreteness is required; the compact-open currying needs local
compactness of the two coordinate spaces. This generalizes the closed-subgroup
restriction clause of Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*,
corrected second edition, Chapter I, §3, Proposition 1.3.6(ii): the ambient
group need only be topological, provided a continuous coset section is chosen.
The whole continuous-function coefficient space has the pointwise subgroup
action, which need not be trivial. -/
noncomputable def coind₁RestrictionIso [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] (B : TopRep.{w} k G)
    (s : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H)) :
    res H.subtype (coind₁ B) ≅
      coind₁ (pointwiseContinuousMap (G ⧸ H) (res H.subtype B)) := by
  let coords : G ≃ₜ H × (G ⧸ H) := {
    toFun t :=
      (⟨t * s (QuotientGroup.mk t⁻¹), by
        have hq := hs (QuotientGroup.mk t⁻¹)
        have hh : (s (QuotientGroup.mk t⁻¹))⁻¹ * t⁻¹ ∈ H :=
          QuotientGroup.eq.mp hq
        simpa only [mul_inv_rev, inv_inv] using H.inv_mem hh⟩,
        QuotientGroup.mk t⁻¹)
    invFun p := p.1.val * (s p.2)⁻¹
    left_inv t := by
      change t * s (QuotientGroup.mk t⁻¹) * (s (QuotientGroup.mk t⁻¹))⁻¹ = t
      simp
    right_inv p := by
      have hq : (QuotientGroup.mk ((p.1.val * (s p.2)⁻¹)⁻¹) : G ⧸ H) = p.2 := by
        calc
          _ = QuotientGroup.mk (s p.2) := by
            apply QuotientGroup.eq.mpr
            simpa only [inv_inv, mul_assoc, inv_mul_cancel, mul_one] using p.1.property
          _ = p.2 := hs p.2
      apply Prod.ext
      · apply Subtype.ext
        change (p.1.val * (s p.2)⁻¹) *
          s (QuotientGroup.mk ((p.1.val * (s p.2)⁻¹)⁻¹)) = p.1.val
        rw [hq]
        simp
      · exact hq
    continuous_toFun := by
      have hc : Continuous (fun t : G => (QuotientGroup.mk t⁻¹ : G ⧸ H)) :=
        QuotientGroup.continuous_mk.comp continuous_inv
      have hh : Continuous (fun t : G => t * s (QuotientGroup.mk t⁻¹)) :=
        continuous_id.mul (s.continuous.comp hc)
      exact (hh.subtype_mk _).prodMk hc
    continuous_invFun :=
      (continuous_subtype_val.comp continuous_fst).mul
        ((s.continuous.comp continuous_snd).inv)
  }
  let coordMap : C(G, H × (G ⧸ H)) := ⟨coords, coords.continuous⟩
  let coordInvMap : C(H × (G ⧸ H), G) := ⟨coords.symm, coords.symm.continuous⟩
  let forward : C(G, B) →L[k] C(H, C(G ⧸ H, B)) := {
    toFun f := ContinuousMap.curry (f.comp coordInvMap)
    map_add' f g := by ext h c; rfl
    map_smul' scalar f := by ext h c; rfl
    cont := ContinuousMap.continuous_curry.comp
      (ContinuousMap.compCLM k B coordInvMap).continuous
  }
  let backward : C(H, C(G ⧸ H, B)) →L[k] C(G, B) := {
    toFun f := (ContinuousMap.uncurry f).comp coordMap
    map_add' f g := by ext t; rfl
    map_smul' scalar f := by ext t; rfl
    cont := (ContinuousMap.compCLM k B coordMap).continuous.comp
      ContinuousMap.continuous_uncurry
  }
  let linearEquiv : C(G, B) ≃L[k] C(H, C(G ⧸ H, B)) :=
    ContinuousLinearEquiv.mk {
      toFun := forward
      invFun := backward
      left_inv := by
        intro f
        apply ContinuousMap.ext
        intro t
        change f (coords.symm (coords t)) = f t
        rw [coords.symm_apply_apply]
      right_inv := by
        intro f
        apply ContinuousMap.ext
        intro h
        apply ContinuousMap.ext
        intro c
        change f (coords (coords.symm (h, c))).1
          (coords (coords.symm (h, c))).2 = f h c
        rw [coords.apply_symm_apply]
      map_add' := forward.map_add
      map_smul' := forward.map_smul }
      forward.continuous backward.continuous
  let equiv : (res H.subtype (coind₁ B)).ρ.Equiv
      (coind₁ (pointwiseContinuousMap (G ⧸ H) (res H.subtype B))).ρ :=
    ContRepresentation.Equiv.mk linearEquiv (by
      intro h₀
      apply ContinuousLinearMap.ext
      intro f
      apply ContinuousMap.ext
      intro h
      apply ContinuousMap.ext
      intro c
      change B.ρ h₀.val (f (h₀.val⁻¹ * (h.val * (s c)⁻¹))) =
        B.ρ h₀.val (f ((h₀⁻¹ * h).val * (s c)⁻¹))
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc])
  refine ⟨ofHom equiv.toContIntertwiningMap,
    ofHom equiv.symm.toContIntertwiningMap, ?_, ?_⟩
  · apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro f
    exact equiv.left_inv f
  · apply TopRep.hom_ext
    apply ContIntertwiningMap.ext
    apply ContinuousLinearMap.ext
    intro f
    exact equiv.right_inv f

/-- The forward isomorphism evaluates the original function at `h * (s c)⁻¹`. -/
theorem coind₁RestrictionIso_hom_apply [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] (B : TopRep.{w} k G)
    (s : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H))
    (f : C(G, B)) (h : H) (c : G ⧸ H) :
    ((coind₁RestrictionIso H B s hs).hom).hom f h c = f (h.val * (s c)⁻¹) := by
  rfl

/-- The inverse recovers the `H`-coordinate by using the inverted left coset. -/
theorem coind₁RestrictionIso_inv_apply [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] (B : TopRep.{w} k G)
    (s : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H))
    (f : C(H, C(G ⧸ H, B))) (t : G) :
    ((coind₁RestrictionIso H B s hs).inv).hom f t =
      f ⟨t * s (QuotientGroup.mk t⁻¹), by
        have hq := hs (QuotientGroup.mk t⁻¹)
        have hh : (s (QuotientGroup.mk t⁻¹))⁻¹ * t⁻¹ ∈ H :=
          QuotientGroup.eq.mp hq
        simpa only [mul_inv_rev, inv_inv] using H.inv_mem hh⟩
        (QuotientGroup.mk t⁻¹) := by
  rfl

/-- Recovering an original function after forward and inverse conversion. -/
theorem coind₁RestrictionIso_inv_hom_apply [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] (B : TopRep.{w} k G)
    (s : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H))
    (f : C(G, B)) :
    ((coind₁RestrictionIso H B s hs).inv).hom
      (((coind₁RestrictionIso H B s hs).hom).hom f) = f := by
  change (((coind₁RestrictionIso H B s hs).hom ≫
    (coind₁RestrictionIso H B s hs).inv).hom f) = f
  rw [(coind₁RestrictionIso H B s hs).hom_inv_id]
  rfl

/-- Recovering a coinduced function after inverse and forward conversion. -/
theorem coind₁RestrictionIso_hom_inv_apply [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] (B : TopRep.{w} k G)
    (s : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H))
    (f : C(H, C(G ⧸ H, B))) :
    ((coind₁RestrictionIso H B s hs).hom).hom
      (((coind₁RestrictionIso H B s hs).inv).hom f) = f := by
  change (((coind₁RestrictionIso H B s hs).inv ≫
    (coind₁RestrictionIso H B s hs).hom).hom f) = f
  rw [(coind₁RestrictionIso H B s hs).inv_hom_id]
  rfl

/-- The forward map respects the full twisted action, with a pointwise
coefficient action rather than a trivial one. -/
theorem coind₁RestrictionIso_action_apply [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] (B : TopRep.{w} k G)
    (s : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H))
    (h₀ h : H) (f : C(G, B)) (c : G ⧸ H) :
    ((coind₁RestrictionIso H B s hs).hom).hom
      ((res H.subtype (coind₁ B)).ρ h₀ f) h c =
        B.ρ h₀.val (f (h₀.val⁻¹ * (h.val * (s c)⁻¹))) := by
  rw [coind₁RestrictionIso_hom_apply]
  rfl

/-- For a fixed section, the restriction isomorphism is natural under
equivariant coefficient maps, using Mathlib's coinduction functor. -/
theorem coind₁RestrictionIso_natural [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] {B D : TopRep.{w} k G}
    (s : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H))
    (f : B ⟶ D) :
    (resFunctor H.subtype).map ((coind₁Functor k G).map f) ≫
        (coind₁RestrictionIso H D s hs).hom =
      (coind₁RestrictionIso H B s hs).hom ≫
        (coind₁Functor k H).map
          (pointwiseContinuousMapMap (Q := G ⧸ H) ((resFunctor H.subtype).map f)) := by
  apply TopRep.hom_ext
  apply ContIntertwiningMap.ext
  apply ContinuousLinearMap.ext
  intro v
  apply ContinuousMap.ext
  intro h
  apply ContinuousMap.ext
  intro c
  change f.hom (v (h.val * (s c)⁻¹)) = f.hom (v (h.val * (s c)⁻¹))
  rfl

/-- The isomorphism remembers its section; equal sections give equal
isomorphisms (the proofs of the projection law are irrelevant). -/
theorem coind₁RestrictionIso_section_congr [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] (B : TopRep.{w} k G)
    (s t : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H))
    (ht : Function.RightInverse t (QuotientGroup.mk : G → G ⧸ H))
    (heq : s = t) :
    coind₁RestrictionIso H B s hs = coind₁RestrictionIso H B t ht := by
  subst t
  rfl

/-- Changing a section changes the `H`-coordinate by the relative
representative `s(c)⁻¹ * t(c) ∈ H`; the isomorphism is not claimed canonical. -/
theorem coind₁RestrictionIso_change_section [LocallyCompactSpace H]
    [LocallyCompactSpace (G ⧸ H)] (B : TopRep.{w} k G)
    (s t : C(G ⧸ H, G))
    (hs : Function.RightInverse s (QuotientGroup.mk : G → G ⧸ H))
    (ht : Function.RightInverse t (QuotientGroup.mk : G → G ⧸ H))
    (f : C(G, B)) (h : H) (c : G ⧸ H) :
    ((coind₁RestrictionIso H B s hs).hom).hom f h c =
      ((coind₁RestrictionIso H B t ht).hom).hom f
        ⟨h.val * ((s c)⁻¹ * t c),
          H.mul_mem h.property (QuotientGroup.eq.mp ((hs c).trans (ht c).symm))⟩ c := by
  rw [coind₁RestrictionIso_hom_apply, coind₁RestrictionIso_hom_apply]
  congr 1
  simp only [mul_assoc, mul_inv_cancel, mul_one]

end TopRep
