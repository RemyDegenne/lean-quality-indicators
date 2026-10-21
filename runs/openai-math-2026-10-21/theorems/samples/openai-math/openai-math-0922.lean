namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula

universe u

variable (M : TransitiveGround.{u}) {G R P L : Type u}

variable [Group G] [PartialOrder R] [PartialOrder P] [OrderTop P] [PartialOrder L]

variable (c : Presentation R) (I0 : ZFSet.{u})

variable (a : PosetAction G P) (s : Presentation P) (b : Presentation L) (d : PosetAction G L)

variable (T T2 : ZFSet.{u}) (valid : ∀ z ∈ T, IsName s z)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)

variable (unions : Realize M.sets SetFormula.union Fin.elim0)

variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

variable (collection : CollectionSchema M.sets)

variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

variable (nodes : b.carrier ∈ M.sets) (hT : T ∈ M.sets)

variable {valid2 : ∀ z ∈ T2, IsName s z}

variable (indices : NiceRefinementIndexSystem M a s b d (natSetCode 1) T T2 valid valid2)

variable (base : L) (directed : ∀ x y : L, ∃ z, x ≤ z ∧ y ≤ z)

variable (system : NiceNameSystem M a s b d base directed T valid)

local notation "Condition" => StageTwoCondition M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

local notation "code" => StageTwoCondition.code M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

local notation "Q" => M.stageTwoForcing c.carrier I0 a s b d T T2 valid

variable (F : FlatConditionSystem M c s (stageOneAssignments I0 T))

variable (first : RefinementIndexLevelCode I0 ∅)

variable (second : RefinementIndexLevelCode
  (M.niceRefinementIndices a s b d (natSetCode 1) T T2 valid) (natSetCode 1))

local notation "inc" => StageTwoCondition.inclusion M c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

local notation "smallOrder" => M.stageTwoConditionSmallOrder c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system

local notation "pres" => M.stageTwoConditionPresentation c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order nodes hT indices base directed system

local notation "smallTop" => M.stageTwoConditionSmallTop c I0 a s b d T T2 valid
  pairing unions powers separation collection carrier order hT base directed system F first second

theorem stageTwo_iteratedPairNameFamily (X : ZFSet.{u}) (n : Nat) :
    letI := smallOrder
    letI := smallTop
    iteratedPairNameFamily ((pres).encode ⊤) X n =
      iteratedPairNameFamily (s.encode ⊤) X n := by
  let := smallOrder
  let := smallTop
  rw [M.stageTwoConditionPresentation_top c I0 a s b d T T2 valid pairing unions powers separation
    collection carrier order nodes hT indices base directed system F first second]

end PartitionPilot.Forcing.TransitiveGround
end
end OAI
