@[expose] public section

universe uR uS uι

namespace ModuleCat.RightExtension

variable {R : Type uR} {S : Type uS} [Ring R] [Ring S]

variable (f : R →+* S)

variable (ι : Type uι) [Fintype ι] [DecidableEq ι]

/-- Coordinatewise scalar extension on a finite canonical right-free module. -/
def rightFreeToSemilinear :
    (ι → R) →ₛₗ[RingHom.op f] (ι → S) where
  toFun x i := f (x i)
  map_add' x y := by
    ext i
    exact f.map_add (x i) (y i)
  map_smul' r x := by
    induction r using MulOpposite.rec' with
    | _ r =>
      ext i
      exact f.map_mul (x i) r

end ModuleCat.RightExtension
end
