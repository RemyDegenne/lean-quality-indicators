/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic
public import Mathlib.CategoryTheory.ConcreteCategory.EpiMono
import Mathlib.Algebra.Category.Grp.EpiMono
import Mathlib.Topology.Algebra.Category.ProfiniteGrp.Limits

/-!
# Monomorphisms and epimorphisms of profinite groups

This file characterizes monomorphisms of profinite groups and profinite
additive groups in terms of their underlying functions, and characterizes
epimorphisms of profinite groups by surjectivity.

These are equivalences in the indicated categories, not a definition of
epimorphism by pointwise surjectivity in arbitrary categories. The reverse
direction for profinite-group epimorphisms uses finite quotients.

## References

- Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Exercise 5(i)–(ii)
  (monomorphisms and epimorphisms); the epimorphism proof here does not use the printed
  hint.
- Mathlib, `Mathlib.CategoryTheory.ConcreteCategory.EpiMono`,
  `Mathlib.Algebra.Category.Grp.EpiMono` and
  `Mathlib.Topology.Algebra.Category.ProfiniteGrp.Basic`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace ProfiniteGrp

noncomputable section

/-- A morphism of profinite groups is a monomorphism exactly when its underlying
function is injective.

This is Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Exercise 5(i),
using Mathlib’s mono API. -/
theorem mono_iff_injective {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    Mono f ↔ Function.Injective f := by
  constructor
  · intro _
    let _ : PreservesLimit (cospan f f) (forget₂ ProfiniteGrp Profinite) :=
      preservesLimit_of_preserves_limit_cone
        (ProfiniteGrp.limitConeIsLimit (cospan f f))
        (Profinite.limitConeIsLimit ((cospan f f) ⋙ forget₂ ProfiniteGrp Profinite))
    let _ : Mono ((forget₂ ProfiniteGrp Profinite).map f) :=
      preserves_mono_of_preservesLimit (forget₂ ProfiniteGrp Profinite) f
    exact (CompHausLike.mono_iff_injective ((forget₂ ProfiniteGrp Profinite).map f)).mp
      inferInstance
  · exact ConcreteCategory.mono_of_injective f

/-- An epimorphism with finite target is surjective. The finite target makes the
permutation-group witnesses in the ordinary group proof into continuous maps
between profinite groups. -/
private theorem surjective_of_epi_of_finite_target
    {G H : ProfiniteGrp.{u}} (f : G ⟶ H) [Epi f] [Finite H] :
    Function.Surjective f := by
  let uf : (forget₂ ProfiniteGrp GrpCat).obj G ⟶
      (forget₂ ProfiniteGrp GrpCat).obj H :=
    (forget₂ ProfiniteGrp GrpCat).map f
  let X := GrpCat.SurjectiveOfEpiAuxs.XWithInfinity uf
  let _ : Finite X := Finite.of_injective
    (fun x : X => match x with
      | .fromCoset y => some y
      | .infinity => none)
    (by
      intro x y hxy
      cases x <;> cases y
      · exact congrArg _ (Option.some.inj hxy)
      · contradiction
      · contradiction
      · rfl)
  let _ : TopologicalSpace (Equiv.Perm X) := ⊥
  let _ : DiscreteTopology (Equiv.Perm X) := ⟨rfl⟩
  let _ : IsTopologicalGroup (Equiv.Perm X) := {}
  let Q : ProfiniteGrp.{u} := ProfiniteGrp.of (Equiv.Perm X)
  let g : H ⟶ Q := ProfiniteGrp.ofHom {
    toFun := GrpCat.SurjectiveOfEpiAuxs.g uf
    map_one' := map_one _
    map_mul' := map_mul _
    continuous_toFun := continuous_of_discreteTopology
  }
  let h : H ⟶ Q := ProfiniteGrp.ofHom {
    toFun := GrpCat.SurjectiveOfEpiAuxs.h uf
    map_one' := map_one _
    map_mul' := map_mul _
    continuous_toFun := continuous_of_discreteTopology
  }
  dsimp [Function.Surjective]
  by_contra! hnot
  obtain ⟨b, hb⟩ := hnot
  have hcomp : f ≫ g = f ≫ h := by
    ext a x
    change GrpCat.SurjectiveOfEpiAuxs.g uf (uf a) x =
      GrpCat.SurjectiveOfEpiAuxs.h uf (uf a) x
    exact DFunLike.congr_fun (DFunLike.congr_fun
      (congr_arg GrpCat.Hom.hom (GrpCat.SurjectiveOfEpiAuxs.comp_eq uf)) a) x
  have hgh : g = h := (cancel_epi f).1 hcomp
  apply GrpCat.SurjectiveOfEpiAuxs.g_ne_h uf b
  · intro hb'
    obtain ⟨a, ha⟩ := hb'
    exact hb a ha
  · have hgh' := congr_arg (fun k : H ⟶ Q => k.hom.toMonoidHom) hgh
    change GrpCat.SurjectiveOfEpiAuxs.g uf =
      GrpCat.SurjectiveOfEpiAuxs.h uf at hgh'
    exact hgh'

/-- A morphism of profinite groups is an epimorphism exactly when its underlying
function is surjective.

This is Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Ch. I §1, Exercise 5(ii);
the proof differs from the printed hint. -/
theorem epi_iff_surjective {G H : ProfiniteGrp.{u}} (f : G ⟶ H) :
    Epi f ↔ Function.Surjective f := by
  constructor
  · intro hf
    let _ : Epi f := hf
    by_contra hsurj
    simp only [Function.Surjective, not_forall, not_exists] at hsurj
    obtain ⟨b, hb⟩ := hsurj
    have hrange : IsClosed (Set.range f) :=
      (isCompact_range f.hom.continuous_toFun).isClosed
    let U : Set H := ((fun x : H => x * b⁻¹) '' Set.range f)ᶜ
    have hUOpen : IsOpen U :=
      ((isClosedMap_mul_right b⁻¹) _ hrange).isOpen_compl
    have hOne : (1 : H) ∈ U := by
      intro hmem
      obtain ⟨x, ⟨a, rfl⟩, hxb⟩ := hmem
      exact hb a (mul_inv_eq_one.mp hxb)
    obtain ⟨N, hN⟩ :=
      ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one hUOpen hOne
    let q := ProfiniteGrp.proj N
    let _ : Epi q := ConcreteCategory.epi_of_surjective q (by
      intro y
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      exact ⟨x, rfl⟩)
    let _ : Epi (f ≫ q) := epi_comp f q
    let _ : Finite (H ⧸ N.toSubgroup) :=
      Subgroup.quotient_finite_of_isOpen N.toSubgroup N.isOpen
    let _ : Finite ((ProfiniteGrp.diagram H).obj N) := by
      change Finite (H ⧸ N.toSubgroup)
      infer_instance
    obtain ⟨a, ha⟩ := surjective_of_epi_of_finite_target (f ≫ q) (q b)
    have hNmem : f a / b ∈ N := by
      apply QuotientGroup.eq_iff_div_mem.mp
      exact ha
    apply hN hNmem
    exact ⟨f a, ⟨a, rfl⟩, by simp [div_eq_mul_inv]⟩
  · exact ConcreteCategory.epi_of_surjective f

end

end ProfiniteGrp

namespace ProfiniteAddGrp

/-- A morphism of profinite additive groups is a monomorphism exactly when its
underlying function is injective. -/
theorem mono_iff_injective {G H : ProfiniteAddGrp.{u}} (f : G ⟶ H) :
    Mono f ↔ Function.Injective f := by
  constructor
  · intro _
    let _ : PreservesLimit (cospan f f) (forget₂ ProfiniteAddGrp Profinite) :=
      preservesLimit_of_preserves_limit_cone
        (ProfiniteAddGrp.limitConeIsLimit (cospan f f))
        (Profinite.limitConeIsLimit ((cospan f f) ⋙ forget₂ ProfiniteAddGrp Profinite))
    let _ : Mono ((forget₂ ProfiniteAddGrp Profinite).map f) :=
      preserves_mono_of_preservesLimit (forget₂ ProfiniteAddGrp Profinite) f
    exact (CompHausLike.mono_iff_injective ((forget₂ ProfiniteAddGrp Profinite).map f)).mp
      inferInstance
  · exact ConcreteCategory.mono_of_injective f

end ProfiniteAddGrp

attribute [to_additive existing] ProfiniteGrp.mono_iff_injective
