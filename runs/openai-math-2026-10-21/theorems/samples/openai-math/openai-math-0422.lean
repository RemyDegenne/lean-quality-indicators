namespace OAI

section

namespace PartitionPilot.Forcing.TransitiveGround

open SetRealization SetFormula

universe u

variable (M : TransitiveGround.{u}) {P : Type u}

variable [PartialOrder P] [OrderTop P] (s : Presentation P)

variable (pairing : Realize M.sets SetFormula.pairing Fin.elim0)

variable (unions : Realize M.sets SetFormula.union Fin.elim0)

variable (powers : Realize M.sets powerSet Fin.elim0) (separation : SeparationSchema M.sets)

variable (collection : CollectionSchema M.sets)

variable (carrier : s.carrier ∈ M.sets) (order : s.conditionOrder ∈ M.sets)

variable {T : ZFSet.{u}} (hT : T ∈ M.sets) (valid : ∀ z ∈ T, IsName s z)

variable {G L : Type u} [Group G] [PartialOrder L]

variable (a : PosetAction G P) (b : Presentation L) (d : PosetAction G L)

variable {T2 : ZFSet.{u}} {valid2 : ∀ z ∈ T2, IsName s z}

variable (indices : NiceRefinementIndexSystem M a s b d ∅ T T2 valid valid2)

include indices in
theorem stageOneFormulaData_fields (C E : L) (U Rf Rc : (M.nameDomain s).names)
    (member : refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val ∈
      M.niceRefinementIndices a s b d ∅ T T2 valid) :
    let idx := refinementIndexCode ∅ (b.encode C) (b.encode E) U.val.val Rf.val.val Rc.val.val
    let data := M.stageOneFormulaData a s b d T T2 valid
    (∀ z, ZFSet.pair idx z ∈ data 1 ↔ z = b.encode C) ∧
    (∀ z, ZFSet.pair idx z ∈ data 2 ↔ z = b.encode E) ∧
    (∀ z, ZFSet.pair idx z ∈ data 3 ↔ z = U.val.val) ∧
    (∀ z, ZFSet.pair idx z ∈ data 4 ↔ z = Rf.val.val) ∧
    (∀ z, ZFSet.pair idx z ∈ data 5 ↔ z = Rc.val.val) :=
  ⟨M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 1,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 2,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 3,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 4,
    M.niceRefinementIndex_field_entry a s b d indices C E U Rf Rc member 5⟩

end PartitionPilot.Forcing.TransitiveGround
end
end OAI
