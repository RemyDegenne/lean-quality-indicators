@[expose] public section

universe u

open CategoryTheory Filter Ultrafilter TopologicalSpace CategoryTheory.Limits FiniteInter

open scoped Topology

local notation "β" => ofTypeMonad Ultrafilter

namespace Compactum

/-- The "free" Compactum functor. -/
def free : Type _ ⥤ Compactum :=
  Monad.free _

end Compactum
end
