public section

namespace TauCeti

open Function Set Submodule

namespace DynkinType

variable {n : ℕ}

/-- The Bourbaki-numbered base of the pinned simply connected root datum of type `Aₙ`. Its support
is the set of the first `n` root indices, carrying the simple roots in Bourbaki order. -/
def typeASimplyConnectedBase (n : ℕ) : (typeASimplyConnectedRootDatum n).Base where
  support := typeASimpleSupport n
  linearIndepOn_root :=
    linearIndepOn_simpleSupport _ _ <| by
      have hcomp : (typeASimplyConnectedRootDatum n).root ∘ typeASimpleIndex n =
          fun i : Fin n => typeAWeight n (i : ℕ) - typeAWeight n ((i : ℕ) + 1) :=
        funext fun i => root_typeASimpleIndex_eq i
      rw [hcomp]
      exact linearIndependent_typeASimpleRoot n
  linearIndepOn_coroot :=
    linearIndepOn_simpleSupport _ _ <| by
      have hcomp : (typeASimplyConnectedRootDatum n).coroot ∘ typeASimpleIndex n =
          fun i : Fin n => typeACoweight n (i : ℕ) - typeACoweight n ((i : ℕ) + 1) :=
        funext fun i => coroot_typeASimpleIndex_eq i
      rw [hcomp]
      exact linearIndependent_typeASimpleCoroot n
  root_mem_or_neg_mem k := by
    have hroot : (typeASimplyConnectedRootDatum n).root k =
        typeAWeight n (((typeAIndexEquiv n).symm k).val.1 : ℕ) -
          typeAWeight n (((typeAIndexEquiv n).symm k).val.2 : ℕ) := rfl
    rw [image_root_typeASimpleSupport, hroot]
    rcases le_total ((((typeAIndexEquiv n).symm k).val.1 : Fin (n + 1)) : ℕ)
        ((((typeAIndexEquiv n).symm k).val.2 : Fin (n + 1)) : ℕ) with h | h
    · exact Or.inl (sub_mem_closure_of_le (typeAWeight n)
        (Nat.lt_succ_iff.mp (((typeAIndexEquiv n).symm k).val.2).isLt) h)
    · refine Or.inr ?_
      rw [neg_sub]
      exact sub_mem_closure_of_le (typeAWeight n)
        (Nat.lt_succ_iff.mp (((typeAIndexEquiv n).symm k).val.1).isLt) h
  coroot_mem_or_neg_mem k := by
    have hcoroot : (typeASimplyConnectedRootDatum n).coroot k =
        typeACoweight n (((typeAIndexEquiv n).symm k).val.1 : ℕ) -
          typeACoweight n (((typeAIndexEquiv n).symm k).val.2 : ℕ) := rfl
    rw [image_coroot_typeASimpleSupport, hcoroot]
    rcases le_total ((((typeAIndexEquiv n).symm k).val.1 : Fin (n + 1)) : ℕ)
        ((((typeAIndexEquiv n).symm k).val.2 : Fin (n + 1)) : ℕ) with h | h
    · exact Or.inl (sub_mem_closure_of_le (typeACoweight n)
        (Nat.lt_succ_iff.mp (((typeAIndexEquiv n).symm k).val.2).isLt) h)
    · refine Or.inr ?_
      rw [neg_sub]
      exact sub_mem_closure_of_le (typeACoweight n)
        (Nat.lt_succ_iff.mp (((typeAIndexEquiv n).symm k).val.1).isLt) h

end DynkinType
end TauCeti
end
