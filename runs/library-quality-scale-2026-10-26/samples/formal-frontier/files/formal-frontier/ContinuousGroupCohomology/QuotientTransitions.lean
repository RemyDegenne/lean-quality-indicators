/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import ContinuousGroupCohomology.ResolutionImage

set_option warningAsError true
set_option backward.isDefEq.respectTransparency.types false

/-!
# Transitions between open-normal quotient stages

For `N ≤ M`, the group homomorphism goes from `G ⧸ N` to `G ⧸ M`, while
the coefficient inclusion goes from `M`-invariants to `N`-invariants.
Consequently the native cochain and cohomology maps run from the coarser
`M`-stage to the finer `N`-stage. No continuity of the joint coefficient action
or compactness of the group is required.
-/

@[expose] public section

universe u v w

open CategoryTheory TopRep

namespace ContinuousCohomology

variable {k : Type u} [Ring k] [TopologicalSpace k]
variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The continuous quotient homomorphism from a finer open-normal stage to a coarser one. -/
def quotientTransitionHom (N M : OpenNormalSubgroup G) (hNM : N ≤ M) :
    (G ⧸ N.toSubgroup) →ₜ* (G ⧸ M.toSubgroup) := by
  letI : DiscreteTopology (G ⧸ N.toSubgroup) :=
    QuotientGroup.discreteTopology N.isOpen
  exact ⟨QuotientGroup.map N.toSubgroup M.toSubgroup (MonoidHom.id G)
    (by intro g hg; exact hNM hg), continuous_of_discreteTopology⟩

@[simp] theorem quotientTransitionHom_mk (N M : OpenNormalSubgroup G) (hNM : N ≤ M)
    (g : G) :
    quotientTransitionHom N M hNM (QuotientGroup.mk' N.toSubgroup g) =
      QuotientGroup.mk' M.toSubgroup g := rfl

theorem quotientTransitionHom_surjective (N M : OpenNormalSubgroup G) (hNM : N ≤ M) :
    Function.Surjective (quotientTransitionHom N M hNM) := by
  intro q
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective M.toSubgroup q
  exact ⟨QuotientGroup.mk' N.toSubgroup g, quotientTransitionHom_mk N M hNM g⟩

theorem quotientTransitionHom_comp_quotient (N M : OpenNormalSubgroup G) (hNM : N ≤ M) :
    (quotientTransitionHom N M hNM).comp (openNormalQuotientHom N) =
      openNormalQuotientHom M := by
  ext g
  exact quotientTransitionHom_mk N M hNM g

theorem quotientTransitionHom_id (N : OpenNormalSubgroup G) :
    quotientTransitionHom N N le_rfl = ContinuousMonoidHom.id _ := by
  ext q
  induction q using QuotientGroup.induction_on with
  | _ g => exact quotientTransitionHom_mk N N le_rfl g

theorem quotientTransitionHom_comp {N M L : OpenNormalSubgroup G}
    (hNM : N ≤ M) (hML : M ≤ L) :
    (quotientTransitionHom M L hML).comp (quotientTransitionHom N M hNM) =
      quotientTransitionHom N L (hNM.trans hML) := by
  ext q
  induction q using QuotientGroup.induction_on with
  | _ g =>
    change quotientTransitionHom M L hML
      (quotientTransitionHom N M hNM (QuotientGroup.mk' N.toSubgroup g)) =
        quotientTransitionHom N L (hNM.trans hML) (QuotientGroup.mk' N.toSubgroup g)
    simp only [quotientTransitionHom_mk]

variable (X : TopRep.{max v w} k G)

/-- Continuous, equivariant inclusion of the coarser invariant coefficients
into the finer ones, viewed as a morphism of `G ⧸ N`-representations. -/
def quotientTransitionIncl {N M : OpenNormalSubgroup G} (hNM : N ≤ M) :
    TopRep.res (quotientTransitionHom N M hNM)
      (TopRep.quotientInvariants M.toSubgroup X) ⟶
        TopRep.quotientInvariants N.toSubgroup X :=
  TopRep.ofHom {
    toContinuousLinearMap :=
      ((X.ρ.restrict M.toSubgroup.subtype).invariants).subtypeL.codRestrict
        ((X.ρ.restrict N.toSubgroup.subtype).invariants)
        (fun x t => x.2 ⟨t.1, hNM t.2⟩)
    isIntertwining' := by
      intro q
      induction q using QuotientGroup.induction_on with
      | _ g =>
        ext x
        change X.ρ g x.1 = X.ρ g x.1
        rfl
  }

@[simp] theorem quotientTransitionIncl_val {N M : OpenNormalSubgroup G} (hNM : N ≤ M)
    (x : TopRep.quotientInvariants M.toSubgroup X) :
    ((quotientTransitionIncl X hNM).hom x).1 = x.1 := rfl

theorem quotientTransitionIncl_injective {N M : OpenNormalSubgroup G} (hNM : N ≤ M) :
    Function.Injective (quotientTransitionIncl X hNM).hom := by
  intro x y hxy
  apply Subtype.ext
  calc
    x.1 = ((quotientTransitionIncl X hNM).hom x).1 :=
      (quotientTransitionIncl_val X hNM x).symm
    _ = ((quotientTransitionIncl X hNM).hom y).1 := congrArg Subtype.val hxy
    _ = y.1 := quotientTransitionIncl_val X hNM y

theorem quotientTransitionIncl_inflate {N M : OpenNormalSubgroup G} (hNM : N ≤ M) :
    (TopRep.resFunctor ((openNormalQuotientHom N) : G →* G ⧸ N.toSubgroup)).map
        (quotientTransitionIncl X hNM) ≫
        TopRep.quotientInvariantsIncl N.toSubgroup X =
      TopRep.quotientInvariantsIncl M.toSubgroup X := by
  ext x
  rfl

/-- Cochain maps agree when their group homomorphisms agree and their
coefficient morphisms agree on underlying values. -/
theorem cochainsMap_congr {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {A : TopRep.{max v w} k G} {B : TopRep.{max v w} k H}
    {φ ψ : H →ₜ* G} (f : TopRep.res φ A ⟶ B) (g : TopRep.res ψ A ⟶ B)
    (hφ : φ = ψ) (hfg : ∀ x : A, f.hom x = g.hom x) :
    cochainsMap φ f = cochainsMap ψ g := by
  subst ψ
  congr 1
  ext x
  exact hfg x

private theorem map_congr {H : Type v} [Group H] [TopologicalSpace H]
    [IsTopologicalGroup H] {A : TopRep.{max v w} k G} {B : TopRep.{max v w} k H}
    {φ ψ : H →ₜ* G} (f : TopRep.res φ A ⟶ B) (g : TopRep.res ψ A ⟶ B)
    (hφ : φ = ψ) (hfg : ∀ x : A, f.hom x = g.hom x) (n : ℕ) :
    map φ f n = map ψ g n := by
  exact congrArg (fun cochainMap => HomologicalComplex.homologyMap cochainMap n)
    (cochainsMap_congr f g hφ hfg)

theorem quotientTransition_cochainsMap_id (N : OpenNormalSubgroup G) :
    cochainsMap (quotientTransitionHom N N (le_refl N))
        (quotientTransitionIncl X (le_refl N)) =
      𝟙 (TopRep.homogeneousCochains (TopRep.quotientInvariants N.toSubgroup X)) := by
  calc
    cochainsMap (quotientTransitionHom N N (le_refl N))
        (quotientTransitionIncl X (le_refl N)) =
        cochainsMap (ContinuousMonoidHom.id (G ⧸ N.toSubgroup))
          (𝟙 (TopRep.quotientInvariants N.toSubgroup X)) := by
            apply cochainsMap_congr _ _ (quotientTransitionHom_id N)
            intro x
            apply Subtype.ext
            rfl
    _ = _ := cochainsMap_id _

theorem quotientTransition_map_id (N : OpenNormalSubgroup G) (n : ℕ) :
    map (quotientTransitionHom N N (le_refl N))
        (quotientTransitionIncl X (le_refl N)) n =
      𝟙 (continuousCohomology n (TopRep.quotientInvariants N.toSubgroup X)) := by
  change HomologicalComplex.homologyMap
    (cochainsMap (quotientTransitionHom N N (le_refl N))
      (quotientTransitionIncl X (le_refl N))) n = _
  rw [quotientTransition_cochainsMap_id X N]
  exact HomologicalComplex.homologyMap_id _ _

theorem quotientTransition_cochainsMap_comp {N M L : OpenNormalSubgroup G}
    (hNM : N ≤ M) (hML : M ≤ L) :
    cochainsMap (quotientTransitionHom N L (hNM.trans hML))
        (quotientTransitionIncl X (hNM.trans hML)) =
      cochainsMap (quotientTransitionHom M L hML) (quotientTransitionIncl X hML) ≫
        cochainsMap (quotientTransitionHom N M hNM) (quotientTransitionIncl X hNM) := by
  calc
    cochainsMap (quotientTransitionHom N L (hNM.trans hML))
        (quotientTransitionIncl X (hNM.trans hML)) =
      cochainsMap ((quotientTransitionHom M L hML).comp
          (quotientTransitionHom N M hNM))
        ((TopRep.resFunctor
            ((quotientTransitionHom N M hNM) : G ⧸ N.toSubgroup →* G ⧸ M.toSubgroup)).map
          (quotientTransitionIncl X hML) ≫ quotientTransitionIncl X hNM) := by
            apply cochainsMap_congr _ _ (quotientTransitionHom_comp hNM hML).symm
            intro x
            apply Subtype.ext
            rfl
    _ = _ := cochainsMap_comp _ _ _ _

theorem quotientTransition_map_comp {N M L : OpenNormalSubgroup G}
    (hNM : N ≤ M) (hML : M ≤ L) (n : ℕ) :
    map (quotientTransitionHom N L (hNM.trans hML))
        (quotientTransitionIncl X (hNM.trans hML)) n =
      map (quotientTransitionHom M L hML) (quotientTransitionIncl X hML) n ≫
        map (quotientTransitionHom N M hNM) (quotientTransitionIncl X hNM) n := by
  calc
    map (quotientTransitionHom N L (hNM.trans hML))
        (quotientTransitionIncl X (hNM.trans hML)) n =
      map ((quotientTransitionHom M L hML).comp
          (quotientTransitionHom N M hNM))
        ((TopRep.resFunctor
            ((quotientTransitionHom N M hNM) : G ⧸ N.toSubgroup →* G ⧸ M.toSubgroup)).map
          (quotientTransitionIncl X hML) ≫ quotientTransitionIncl X hNM) n := by
            apply map_congr _ _ (quotientTransitionHom_comp hNM hML).symm
              (fun x => by apply Subtype.ext; rfl)
    _ = _ := map_comp _ _ _ _ _

/-- Inflation from the coarser stage factors through the finer one on native cochains. -/
theorem quotientTransition_cochainsMap_inflate {N M : OpenNormalSubgroup G}
    (hNM : N ≤ M) :
    cochainsMap (openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) =
      cochainsMap (quotientTransitionHom N M hNM) (quotientTransitionIncl X hNM) ≫
        cochainsMap (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) := by
  convert (cochainsMap_comp (quotientTransitionHom N M hNM) (openNormalQuotientHom N)
      (quotientTransitionIncl X hNM)
      (TopRep.quotientInvariantsIncl N.toSubgroup X)) using 1
  congr 1

/-- Inflation from the coarser stage factors through the finer one in every degree. -/
theorem quotientTransition_map_inflate {N M : OpenNormalSubgroup G}
    (hNM : N ≤ M) (n : ℕ) :
    map (openNormalQuotientHom M)
        (TopRep.quotientInvariantsIncl M.toSubgroup X) n =
      map (quotientTransitionHom N M hNM) (quotientTransitionIncl X hNM) n ≫
        map (openNormalQuotientHom N)
          (TopRep.quotientInvariantsIncl N.toSubgroup X) n := by
  convert (map_comp (quotientTransitionHom N M hNM) (openNormalQuotientHom N)
      (quotientTransitionIncl X hNM)
      (TopRep.quotientInvariantsIncl N.toSubgroup X) n) using 1
  congr 1

end ContinuousCohomology
