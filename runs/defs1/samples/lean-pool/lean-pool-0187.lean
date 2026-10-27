@[expose] public section

/-- Type class stating that `x : ℝ` carries a `ComputableℝSeq`: an explicit sequence of rational
interval approximations converging to `x`. Like `Decidable`, it carries data with it, and
classically every real number admits such a sequence; its value lies in the explicit
approximations it provides, not in a computability guarantee. -/
class IsComputable (x : ℝ) : Type where
    /-- A computable sequence representing `x`. -/
    seq : ComputableℝSeq
    /-- The sequence converges to `x`. -/
    prop : seq.val = x

end
