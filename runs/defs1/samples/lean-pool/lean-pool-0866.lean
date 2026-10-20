@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

namespace MovingSofa.GerverAreaCert

open SI

/-- Left horizontal bound of the covering rectangle of `(r, j)`. -/
def rectLoZ (r j : ℕ) : ℤ :=
  if rowFwd r then (contactZ (rowBase r j) (rowKind r)).1.lo
  else (contactZ (rowBase r j + 1) (rowKind r)).1.lo

end MovingSofa.GerverAreaCert
end
end
end
end
end
end
end
