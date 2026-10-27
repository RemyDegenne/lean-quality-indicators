@[expose] public section

universe u v w

namespace ProfiniteGrp

namespace IsProcyclic

/-- The primewise exponents of a procyclic profinite group, formed using a
chosen generator and the fixed universe-zero p-adic source. Independent of
the chosen generator by `exponents_eq_of_generator`. -/
noncomputable def exponents {G : ProfiniteGrp.{u}} (hG : IsProcyclic G) :
    Nat.Primes → ℕ∞ :=
  primewisePadicKernelExponents (primewisePadicBaseMapOfGenerator G hG.choose)

end IsProcyclic
end ProfiniteGrp
end
