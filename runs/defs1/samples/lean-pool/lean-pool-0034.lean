@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace GerverSofa.PartF.Phases

/-- The five-branch closed formula for the rotation path. -/
def closedPath (d : Reduced.Params) (t : ℝ) : Point :=
  if t ≤ d.phi then closed1 d t
  else if t ≤ d.theta then closed2 d t
  else if t ≤ Real.pi / 2 - d.theta then closed3 d t
  else if t ≤ Real.pi / 2 - d.phi then closed4 d t
  else closed5 d t

end GerverSofa.PartF.Phases
end
end
end
end
end
end
end
end
