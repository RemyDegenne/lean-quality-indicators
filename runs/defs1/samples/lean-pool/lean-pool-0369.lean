@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace MovingSofa

/-- A normal half-plane: `upper` chooses the greater side, `strict` its open version. -/
def normalHalfPlane (t : Real.Angle) (h : ℝ) (upper strict : Bool) : Set Point :=
  {p | if upper then
    if strict then h < inner ℝ p (normalVector t) else h ≤ inner ℝ p (normalVector t)
  else
    if strict then inner ℝ p (normalVector t) < h else inner ℝ p (normalVector t) ≤ h}

end MovingSofa
end
end
end
end
end
end
end
end
end
end
end
