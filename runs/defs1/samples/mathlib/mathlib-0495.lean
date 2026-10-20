@[expose] public section

universe u v

namespace MvPFunctor

open TypeVec

open MvFunctor

variable {n : ℕ} (P : MvPFunctor.{u} (n + 1))

/-- W-types are functorial -/
def wMap {α β : TypeVec n} (g : α ⟹ β) : P.W α → P.W β := fun x => g <$$> x

end MvPFunctor
end
