@[expose] public section

namespace RS

namespace EdgeSubset

open Fragment

@[reducible] local instance liftBaseOrder (n : ℕ) :
    LinearOrder (Fin (0 + n) ⊕ Fin (n + 0)) :=
  sumLexLinearOrder _ _

@[reducible] local instance liftOrderSucc (n : ℕ) :
    LinearOrder (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) :=
  sumLexLinearOrder _ _

@[reducible] local instance liftSurvOrder (n : ℕ) :
    LinearOrder (SurvivingLabel
      (Fin (0 + n + 1) ⊕ Fin (n + 1 + 0)) (cutL n) (cutR n)) :=
  sumLexSubtypeLinearOrder _ _ _

@[reducible] local instance liftTopOrder :
    LinearOrder (Fin 0 ⊕ Fin 0) :=
  sumLexLinearOrder _ _

/-- The flag the right half of the `m`-th cut points at. -/
noncomputable abbrev cutFlagR {t : ℕ} (F G : Fragment (Fin t))
    (m : Fin t) : (closeBase F G).Flag :=
  (closeBase F G).pairing ((closeBase F G).boundaryFlag (intR t m))

end EdgeSubset
end RS
end
