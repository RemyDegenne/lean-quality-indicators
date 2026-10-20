public section

universe u v

namespace List

variable {F G : Type u → Type u}

variable [Applicative F] [Applicative G]

section Traverse

variable {α' β' : Type u} (f : α' → F β')

variable [LawfulApplicative F]

@[simp]
theorem traverse_append :
    ∀ as bs : List α', traverse f (as ++ bs) = (· ++ ·) <$> traverse f as <*> traverse f bs
  | [], bs => by simp [functor_norm]
  | a :: as, bs => by simp [traverse_append as bs, functor_norm]; congr

end Traverse
end List
end
