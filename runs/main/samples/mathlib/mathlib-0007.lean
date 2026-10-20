@[expose] public section

namespace Submodule

open LinearMap

variable {ι R : Type*} [CommRing R]

variable {Ms : ι → Type*} [∀ i, AddCommGroup (Ms i)] [∀ i, Module R (Ms i)]

variable {N : Type*} [AddCommGroup N] [Module R N]

variable {Ns : ι → Type*} [∀ i, AddCommGroup (Ns i)] [∀ i, Module R (Ns i)]

namespace quotientPi_aux

variable (p : ∀ i, Submodule R (Ms i))

theorem map_add (x y : ((i : ι) → Ms i) ⧸ pi Set.univ p) :
    toFun p (x + y) = toFun p x + toFun p y :=
  LinearMap.map_add (quotientPiLift p (fun i => (p i).mkQ) fun i => (ker_mkQ (p i)).ge) x y

end quotientPi_aux
end Submodule
end
