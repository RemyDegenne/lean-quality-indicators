namespace Ihara

open CongruenceSubgroup

open scoped MatrixGroups

def iharaAmalgam (N q : ℕ) : Type :=
  Monoid.PushoutI (iharaEdge N q)

end Ihara
