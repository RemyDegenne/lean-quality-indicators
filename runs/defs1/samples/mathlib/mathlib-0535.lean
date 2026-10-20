@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} [NonAssocSemiring R]

section SubsemiringClass

variable [SetLike S R] [hSR : SubsemiringClass S R] (s : S)

namespace SubsemiringClass

/-- The natural ring hom from a subsemiring of semiring `R` to `R`. -/
def subtype : s →+* R :=
  { SubmonoidClass.subtype s, AddSubmonoidClass.subtype s with toFun := (↑) }

end SubsemiringClass
end SubsemiringClass
end
