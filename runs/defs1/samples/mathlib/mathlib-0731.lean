@[expose] public section

namespace CoxeterSystem

open List Function

variable {B W : Type*} [Group W]

variable {M : CoxeterMatrix B} (cs : CoxeterSystem M W)

local prefix:100 "s " => cs.simple

local prefix:100 "π " => cs.wordProd

local prefix:100 "ℓ " => cs.length

/-- The proposition that `ω` is reduced; that is, it has minimal length among all words that
represent the same element of `W`. -/
def IsReduced (ω : List B) : Prop := ℓ (π ω) = ω.length

end CoxeterSystem
end
