open Lean

macro "alias!" doc:docComment Alias:ident Source:ident : command => `(

@[expose] public section

$doc:docComment

namespace $Alias

universe u

@[simp] theorem $(mkIdent `val_symm) : .symm $(mkVal Alias) = $(mkOf Alias) := rfl

end $Alias
end $doc:docComment
