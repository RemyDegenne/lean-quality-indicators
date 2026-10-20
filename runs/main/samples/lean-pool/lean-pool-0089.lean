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

notation "□'^[" n:90 "]" l:80 => List.multibox n l

notation "◇'^[" n:90 "]" l:80 => List.multidia n l

prefix:80 "□'" => List.box

prefix:80 "◇'" => List.dia

notation "□'⁻¹^[" n:90 "]" l:80 => List.premultibox n l

notation "◇'⁻¹^[" n:90 "]" l:80 => List.premultidia n l

prefix:80 "□'⁻¹" => List.prebox

prefix:80 "◇'⁻¹" => List.predia

namespace List

variable {l : List F} {s : Set F} {φ : F}

variable [DecidableEq F]

section «lp_section_8»

variable [Box F]

lemma box_nil : (□'([] : List F)) = [] := by simp;

end «lp_section_8»
end List
end «lp_section_1»
end
