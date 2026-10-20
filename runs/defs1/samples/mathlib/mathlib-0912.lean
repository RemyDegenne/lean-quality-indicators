@[expose] public section

set_option autoImplicit true

/-- A monad to generate random objects using the generator type `g`. -/
abbrev RandG (g : Type) := RandGT g Id

end
