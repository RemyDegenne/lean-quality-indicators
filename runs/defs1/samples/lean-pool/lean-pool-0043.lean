@[expose] public section

open Function

prefix:76 "□" => Box.box

prefix:76 "⊡" => boxdot

notation:76 "□^[" n:90 "]" φ:80 => multibox n φ

prefix:76 "◇" => Dia.dia

prefix:76 "diaDot" => diadot

notation:76 "◇^[" n:90 "]" φ:80 => multidia n φ

section «lp_section_1»

open LO (Box Dia)

variable {F : Type*}

notation:80 "□''^[" n:90 "]" s:80 => Set.multibox n s

notation:80 "◇''^[" n:90 "]" s:80 => Set.multidia n s

prefix:80 "□''" => Set.box

prefix:80 "◇''" => Set.dia

notation:80 "□''⁻¹^[" n:90 "]" s:80 => Set.premultibox n s

notation:80 "◇''⁻¹^[" n:90 "]" s:80 => Set.premultidia n s

prefix:80 "□''⁻¹" => Set.prebox

prefix:80 "◇''⁻¹" => Set.predia

section «lp_section_4»

variable [DecidableEq F]

/-- Imported declaration from the Incompleteness formalization. -/
protected abbrev Finset.modalBox [Box F] : Finset F → Finset F := Finset.multibox (n := 1)

end «lp_section_4»
end «lp_section_1»
end
