@[expose] public section

open scoped Ring

variable {R : Type*}

/-- `-⅟a` is the inverse of `-a` -/
@[instance_reducible]
def invertibleNeg [Mul R] [One R] [HasDistribNeg R] (a : R) [Invertible a] : Invertible (-a) :=
  ⟨-⅟a, by simp, by simp⟩

end
