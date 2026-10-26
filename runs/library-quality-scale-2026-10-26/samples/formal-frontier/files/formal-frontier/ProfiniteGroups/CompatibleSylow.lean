/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.GroupTheory.Sylow
public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

@[expose] public section

/-!
# Compatible Sylow subgroups of finite quotients

A surjective cofiltered diagram of finite groups admits compatible choices of Sylow
subgroups, even after one coordinate has been specified. The canonical diagram of
finite quotients of a profinite group is such a diagram.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §6, proof of (1.6.9)
  (compatible Sylow subgroups in finite quotients).
- Mathlib, `Mathlib.GroupTheory.Sylow`, `Mathlib.CategoryTheory.CofilteredSystem` and
  `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits`.
-/

namespace CompatibleSylow

open CategoryTheory

universe u v w

variable {J : Type u} [Category.{w} J]

/-- The diagram of Sylow subgroups associated to a finite-group diagram with
surjective transition maps. -/
noncomputable def system (p : ℕ) (hp : p.Prime) (F : J ⥤ FiniteGrp.{v})
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) : J ⥤ Type v := by
  letI : Fact p.Prime := ⟨hp⟩
  exact {
    obj := fun i => Sylow p (F.obj i)
    map := fun {i j} (f : i ⟶ j) => ↾(fun P : Sylow p (F.obj i) =>
      P.mapSurjective (f := ConcreteCategory.hom (C := FiniteGrp.{v}) (F.map f)) (hF f))
    map_id := by
      intro i
      apply ConcreteCategory.hom_ext
      intro P
      apply Sylow.ext
      change Subgroup.map (ConcreteCategory.hom (C := FiniteGrp.{v}) (F.map (𝟙 i)))
        (P : Subgroup (F.obj i)) = P
      rw [F.map_id]
      change (P : Subgroup (F.obj i)).map (MonoidHom.id _) = P
      exact Subgroup.map_id (K := (P : Subgroup (F.obj i)))
    map_comp := by
      intro i j k f g
      apply ConcreteCategory.hom_ext
      intro P
      apply Sylow.ext
      change Subgroup.map (ConcreteCategory.hom (C := FiniteGrp.{v}) (F.map (f ≫ g)))
          (P : Subgroup (F.obj i)) =
        Subgroup.map (ConcreteCategory.hom (C := FiniteGrp.{v}) (F.map g))
          (Subgroup.map (ConcreteCategory.hom (C := FiniteGrp.{v}) (F.map f))
            (P : Subgroup (F.obj i)))
      rw [F.map_comp]
      simp only [Subgroup.map_map]
      rfl }

/-- Compatible Sylow choices in a surjective cofiltered finite-group diagram,
extending a prescribed choice at any index. -/
theorem exists_system_with [IsCofilteredOrEmpty J] (p : ℕ) (hp : p.Prime)
    (F : J ⥤ FiniteGrp.{v})
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f))
    (i : J) (P : Sylow p (F.obj i)) :
    ∃ s : (system p hp F hF).sections, s.val i = P := by
  let : Fact p.Prime := ⟨hp⟩
  let : ∀ j, Nonempty ((system p hp F hF).obj j) := fun _ => Sylow.nonempty
  let : ∀ j, Finite ((system p hp F hF).obj j) := fun j => by
    let P : Sylow p (F.obj j) := Sylow.nonempty.some
    exact P.finite_of_finiteIndex
  have hsur : ∀ ⦃a b : J⦄ (f : a ⟶ b),
      Function.Surjective ((system p hp F hF).map f) :=
    fun {a b} (f : a ⟶ b) => Sylow.mapSurjective_surjective (hF f) p
  exact (Functor.eval_section_surjective_of_surjective
    (F := system p hp F hF) hsur i) P

/-- A compatible Sylow choice in a surjective cofiltered finite-group diagram. -/
theorem exists_system [IsCofilteredOrEmpty J] (p : ℕ) (hp : p.Prime)
    (F : J ⥤ FiniteGrp.{v})
    (hF : ∀ ⦃i j : J⦄ (f : i ⟶ j), Function.Surjective (F.map f)) :
    Nonempty (system p hp F hF).sections := by
  let : ∀ j, Nonempty ((system p hp F hF).obj j) := fun _ => Sylow.nonempty
  let : ∀ j, Finite ((system p hp F hF).obj j) := fun j => by
    let P : Sylow p (F.obj j) := Sylow.nonempty.some
    exact P.finite_of_finiteIndex
  obtain ⟨s, hs⟩ := nonempty_sections_of_finite_cofiltered_system (system p hp F hF)
  exact ⟨⟨s, hs⟩⟩

end CompatibleSylow

namespace ProfiniteGrp

open CategoryTheory

universe u

/-- Every transition in the canonical finite quotient diagram is surjective. -/
theorem quotientSylowTransition_surjective (G : ProfiniteGrp.{u})
    ⦃U V : OpenNormalSubgroup G⦄ (f : U ⟶ V) :
    Function.Surjective (G.toFiniteQuotientFunctor.map f) := by
  change Function.Surjective (QuotientGroup.map (U : Subgroup G) (V : Subgroup G)
    (MonoidHom.id G) (leOfHom f))
  intro x
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
  exact ⟨QuotientGroup.mk g, rfl⟩

/-- Compatible Sylow subgroups of the canonical finite open-normal quotient diagram. -/
noncomputable def compatibleSylow (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime) :
    OpenNormalSubgroup G ⥤ Type u :=
  CompatibleSylow.system p hp G.toFiniteQuotientFunctor
    (G.quotientSylowTransition_surjective)

/-- A compatible family takes a Sylow subgroup at each finite quotient and
respects every quotient transition. -/
structure CompatibleSylowFamily (G : ProfiniteGrp.{u}) (p : ℕ) (hp : p.Prime) where
  toSection : (G.compatibleSylow p hp).sections

/-- Every prescribed Sylow subgroup at one finite quotient extends to a
compatible family over all finite open-normal quotients. -/
theorem exists_compatibleSylowFamily_with (G : ProfiniteGrp.{u}) (p : ℕ)
    (hp : p.Prime) (U : OpenNormalSubgroup G)
    (P : Sylow p (G ⧸ (U : Subgroup G))) :
    ∃ s : G.CompatibleSylowFamily p hp, s.toSection.val U = P := by
  obtain ⟨s, hs⟩ := CompatibleSylow.exists_system_with p hp G.toFiniteQuotientFunctor
    (G.quotientSylowTransition_surjective) U P
  exact ⟨⟨s⟩, hs⟩

/-- Existence of a compatible Sylow family on all finite open-normal quotients. -/
theorem exists_compatibleSylowFamily (G : ProfiniteGrp.{u}) (p : ℕ)
    (hp : p.Prime) : Nonempty (G.CompatibleSylowFamily p hp) := by
  obtain ⟨s⟩ := CompatibleSylow.exists_system p hp G.toFiniteQuotientFunctor
    (G.quotientSylowTransition_surjective)
  exact ⟨⟨s⟩⟩

/-- Evaluate a compatible Sylow family at an open normal subgroup. -/
def CompatibleSylowFamily.at {G : ProfiniteGrp.{u}} {p : ℕ} {hp : p.Prime}
    (s : G.CompatibleSylowFamily p hp) (U : OpenNormalSubgroup G) :
    Sylow p (G ⧸ (U : Subgroup G)) := s.toSection.val U

/-- Two compatible Sylow families are equal when they agree at every finite quotient. -/
@[ext]
theorem CompatibleSylowFamily.ext {G : ProfiniteGrp.{u}} {p : ℕ} {hp : p.Prime}
    {s t : G.CompatibleSylowFamily p hp}
    (h : ∀ U : OpenNormalSubgroup G, s.at U = t.at U) : s = t := by
  cases s with
  | mk section_s =>
    cases t with
    | mk section_t =>
      congr 1
      exact (Functor.sections_ext_iff).2 h

/-- The chosen Sylow subgroup at a finer quotient maps to the choice at a
coarser quotient. -/
theorem CompatibleSylowFamily.map_at {G : ProfiniteGrp.{u}} {p : ℕ}
    {hp : p.Prime} (s : G.CompatibleSylowFamily p hp)
    ⦃U V : OpenNormalSubgroup G⦄ (f : U ⟶ V) :
    (G.compatibleSylow p hp).map f (s.at U) = s.at V :=
  s.toSection.property f

/-- Explicit subgroup-image compatibility for an inclusion of open normal subgroups. -/
theorem CompatibleSylowFamily.map_at_subgroup {G : ProfiniteGrp.{u}} {p : ℕ}
    {hp : p.Prime} (s : G.CompatibleSylowFamily p hp)
    {U V : OpenNormalSubgroup G} (h : U ≤ V) :
    (s.at U : Subgroup (G ⧸ (U : Subgroup G))).map
      (QuotientGroup.map (U : Subgroup G) (V : Subgroup G) (MonoidHom.id G) h) =
        (s.at V : Subgroup (G ⧸ (V : Subgroup G))) := by
  have hs := s.map_at (homOfLE h)
  exact congrArg (fun Q : Sylow p (G ⧸ (V : Subgroup G)) =>
    (Q : Subgroup (G ⧸ (V : Subgroup G)))) hs

end ProfiniteGrp
