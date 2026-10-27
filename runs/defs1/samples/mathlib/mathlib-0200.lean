@[expose] public section

universe u v w

variable {R : Type u} {S : Type v} {T : Type w} [NonAssocSemiring R] (M : Submonoid R)

variable [NonAssocSemiring S] [NonAssocSemiring T]

namespace Subsemiring

/-- Given `Subsemiring`s `s`, `t` of semirings `R`, `S` respectively, `s.prod t` is `s × t`
as a subsemiring of `R × S`. -/
def prod (s : Subsemiring R) (t : Subsemiring S) : Subsemiring (R × S) :=
  { s.toSubmonoid.prod t.toSubmonoid, s.toAddSubmonoid.prod t.toAddSubmonoid with
    carrier := s ×ˢ t }

end Subsemiring
end
