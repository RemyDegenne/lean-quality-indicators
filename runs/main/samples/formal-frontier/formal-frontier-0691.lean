@[expose] public section

universe uR uS uM

open CategoryTheory

namespace ModuleCat

@[simp]
theorem restrictScalarsEndEquiv_apply {R : Type uR} {S : Type uS} [Ring R] [Ring S]
    (f : R →+* S) (hf : Function.Surjective f) (M : ModuleCat.{uM} S)
    (g : Module.End S M) (x : M) :
    restrictScalarsEndEquiv f hf M g x = g x := rfl

end ModuleCat
end
