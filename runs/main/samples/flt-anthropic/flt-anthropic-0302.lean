namespace P2MW.S_EisensteinWeightOne_e1Chi3IsModular

namespace S17E1

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

p2m_reactivate

section File_FLT_AnalyticCore_OrbitCountMultiplicative

namespace FLT

namespace AnalyticCore

open Finset

namespace HexInt

scoped instance : Zero HexInt := ⟨⟨0, 0⟩⟩

scoped instance : One HexInt := ⟨⟨1, 0⟩⟩

scoped instance : Add HexInt := ⟨fun z w => ⟨z.re + w.re, z.im + w.im⟩⟩

scoped instance : Neg HexInt := ⟨fun z => ⟨-z.re, -z.im⟩⟩

scoped instance : Mul HexInt :=
  ⟨fun z w => ⟨z.re * w.re - z.im * w.im, z.re * w.im + z.im * w.re + z.im * w.im⟩⟩

scoped instance addCommGroup : AddCommGroup HexInt := by
  refine
  { sub := fun a b => a + -b
    nsmul := @nsmulRec HexInt ⟨0⟩ ⟨(· + ·)⟩
    zsmul := @zsmulRec HexInt ⟨0⟩ ⟨(· + ·)⟩ ⟨Neg.neg⟩ (@nsmulRec HexInt ⟨0⟩ ⟨(· + ·)⟩)
    add_assoc := ?_
    zero_add := ?_
    add_zero := ?_
    neg_add_cancel := ?_
    add_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp [add_comm, add_left_comm]

scoped instance addGroupWithOne : AddGroupWithOne HexInt :=
  { HexInt.addCommGroup with
    natCast := fun n => ⟨(n : ℤ), 0⟩
    intCast := fun n => ⟨n, 0⟩ }

scoped instance commRing : CommRing HexInt := by
  refine
  { HexInt.addGroupWithOne with
    npow := @npowRec HexInt ⟨1⟩ ⟨(· * ·)⟩
    add_comm := ?_
    left_distrib := ?_
    right_distrib := ?_
    zero_mul := ?_
    mul_zero := ?_
    mul_assoc := ?_
    one_mul := ?_
    mul_one := ?_
    mul_comm := ?_ } <;>
  intros <;>
  ext <;>
  simp <;>
  ring

scoped instance : Nontrivial HexInt :=
  ⟨⟨0, 1, fun h => one_ne_zero (α := ℤ) (by simpa using congrArg HexInt.re h.symm)⟩⟩

scoped instance : Div HexInt :=
  ⟨fun x y => ⟨nearestDiv (x * y.conj).re y.norm, nearestDiv (x * y.conj).im y.norm⟩⟩

scoped instance : Mod HexInt := ⟨fun x y => x - y * (x / y)⟩

scoped instance : EuclideanDomain HexInt :=
  { HexInt.commRing, (inferInstance : Nontrivial HexInt) with
    quotient := (· / ·)
    quotient_zero := div_zero'
    remainder := (· % ·)
    quotient_mul_add_remainder_eq := fun a b => by rw [mod_def]; ring
    r := _
    r_wellFounded := (measure (Int.natAbs ∘ norm)).wf
    remainder_lt := fun a _ hb => natAbs_norm_mod_lt a hb
    mul_left_not_lt := fun a _ hb => not_lt.mpr (natAbs_norm_le_natAbs_norm_mul a hb) }

theorem conj_mem_unitFinset {u : HexInt} (hu : u ∈ unitFinset) : u.conj ∈ unitFinset := by
  fin_cases hu <;> decide

end HexInt
end AnalyticCore
end FLT
end File_FLT_AnalyticCore_OrbitCountMultiplicative
end S17E1
end P2MW.S_EisensteinWeightOne_e1Chi3IsModular
