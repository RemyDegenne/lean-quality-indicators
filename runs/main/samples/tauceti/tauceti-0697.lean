public section

namespace TauCeti

namespace zHat

universe u v

open Additive Multiplicative

section AddLift

variable {A : Type v} [AddZeroClass A] (f : ∀ n : ℕ+, A →+ ZMod n)
  (hf : ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n), (ZMod.castHom h (ZMod m) : ZMod n →+ ZMod m).comp (f n) =
    f m)

theorem continuous_addLift [TopologicalSpace A]
    (hcont : ∀ n : ℕ+, Continuous (f n : A → ZMod n)) : Continuous (addLift f hf) :=
  continuous_iff_forall_continuous_toZMod.mpr fun n ↦ by
    simpa only [toZMod_addLift] using hcont n

end AddLift
end zHat
end TauCeti
end
