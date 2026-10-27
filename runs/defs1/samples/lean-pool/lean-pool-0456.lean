@[expose] public section

noncomputable section

namespace ConwaySoifer

/-- The centre and boundary vertices used to assign distinct covering owners. -/
def anchor : Fin 10 → Point :=
  ![(0, 0), (1, 0), (0, 1), (-1, 1), (-1, 0), (0, -1), (1, -1), (1, 1), (-2, 1), (1, -2)]

end ConwaySoifer
end
end
