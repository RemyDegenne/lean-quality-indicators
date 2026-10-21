namespace OAI

section

namespace ExactQuantumFactoring.NativeAIG

open BitStackProgram BitStackProgram.Procedure

lemma zipVec_bound {C B : ℕ} {op : BinOp} (hop : BinBound C op) {r : Graph} {lhs rhs : List Ref}
    (hg : Bounded B r) (hl : RefsBound B lhs) (hr : RefsBound B rhs) :
    Bounded (B+(C+1)*lhs.length) (zipVec op r lhs rhs).1 ∧
    RefsBound (B+(C+1)*lhs.length) (zipVec op r lhs rhs).2 ∧
    (zipVec op r lhs rhs).2.length=lhs.length := by
  let s : AddState:=⟨⟨B,r,lhs,rhs,0,(0,false),[]⟩,
    hg,hl,hr,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _,by intro a ha;cases ha⟩
  have hb:=zipState_budget hop s
  have ho:=(zipState hop s).property
  rw [←zipState_value hop s]
  unfold AddOK at ho
  rw [hb] at ho
  exact ⟨ho.1,ho.2.2.2.2.2,zipState_length hop s⟩

end ExactQuantumFactoring.NativeAIG
end
end OAI
