/-
SPDX-License-Identifier: Apache-2.0
Authors: Formal Frontier Agents
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree

public section

/-!
# Finite presentations from finite local bases

The finite generators in a local basis and the empty relations in its native
presentation give local finite presentation. Both finiteness and local freeness
refer to the same local generator data; no refinement of separate covers is
assumed.
-/

open CategoryTheory

universe w u v₁ u₁

namespace SheafOfModules.LocalGeneratorsData

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}
  {R : Sheaf J RingCat.{u}}
  [∀ X, HasSheafify (J.over X) AddCommGrpCat.{u}]
  [∀ X, (J.over X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  {M : SheafOfModules.{u} R}

private theorem finitePresentationData (q : M.LocalGeneratorsData.{w})
    [q.IsLocallyFreeData] [q.IsFiniteType] :
    q.quasiCoherentData.IsFinitePresentation := by
  constructor
  intro i
  constructor
  · change (q.generators i).IsFiniteType
    exact SheafOfModules.LocalGeneratorsData.IsFiniteType.isFiniteType i
  · constructor
    change Finite (ULift Empty)
    infer_instance

/-- A local basis with finitely many generators on each chart gives local finite
presentation. The covering family need not be finite, and the numbers of generators
may vary between charts. Both hypotheses concern the same local generator datum. -/
theorem isFinitePresentation_of_isLocallyFreeData (q : M.LocalGeneratorsData.{w})
    [q.IsLocallyFreeData] [q.IsFiniteType] : M.IsFinitePresentation := by
  let : q.quasiCoherentData.IsFinitePresentation := finitePresentationData q
  refine ⟨q.quasiCoherentData.shrink, ?_⟩
  constructor
  intro i
  change (q.quasiCoherentData.presentation i.2.choose).IsFinite
  infer_instance

end SheafOfModules.LocalGeneratorsData
