@[expose] public section

open GenContFract

open GenContFract (of)

open Int

variable {K : Type*} {v : K} {n : ℕ} [Field K] [LinearOrder K] [IsStrictOrderedRing K] [FloorRing K]

variable (v)

/-- Creates the continued fraction of a value. -/
def ContFract.of : ContFract K :=
  ⟨SimpContFract.of v, SimpContFract.of_isContFract v⟩

end
