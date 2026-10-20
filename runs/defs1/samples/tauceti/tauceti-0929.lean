public section

namespace IsDedekindDomain.HeightOneSpectrum

variable {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]

variable (B) [FaithfulSMul R B]

/-- The nonzero prime ideals of `B` lying over a nonzero prime `v` of `R` are precisely
`Ideal.primesOver v.asIdeal B`. Injectivity of the algebra map ensures that an ideal lying
above `v` is nonzero; neither ring needs to be a Dedekind domain. -/
def liesOverEquivPrimesOver (v : HeightOneSpectrum R) :
    {w : HeightOneSpectrum B // w.asIdeal.LiesOver v.asIdeal} ≃ v.asIdeal.primesOver B where
  toFun w := ⟨w.1.asIdeal, w.1.isPrime, w.2⟩
  invFun Q := ⟨⟨Q.1, Q.2.1, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot Q.1⟩, Q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

end IsDedekindDomain.HeightOneSpectrum
end
