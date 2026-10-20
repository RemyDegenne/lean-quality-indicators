@[expose] public section

universe u v w

open List

variable {α : Type u} {β : α → Type v}

/-- `AList β` is a key-value map stored as a `List` (i.e. a linked list).
  It is a wrapper around certain `List` functions with the added constraint
  that the list have unique keys. -/
structure AList (β : α → Type v) : Type max u v where
  /-- The underlying `List` of an `AList` -/
  entries : List (Sigma β)
  /-- There are no duplicate keys in `entries` -/
  nodupKeys : entries.NodupKeys

end
