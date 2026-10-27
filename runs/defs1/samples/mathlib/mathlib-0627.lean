@[expose] public section

variable {α : Type*} [LE α]

export SupSet (sSup)

export InfSet (sInf)

/-- `OrderInfSet α` expresses that `α` is equipped with the operation `sInf` that returns
the greatest lower bound of a set whenever one exists. -/
@[to_dual existing]
class OrderInfSet (α : Type*) [LE α] extends InfSet α where
  protected isGLB_sInf_of_isGLB s a : IsGLB s a → IsGLB s (sInf s)

end
