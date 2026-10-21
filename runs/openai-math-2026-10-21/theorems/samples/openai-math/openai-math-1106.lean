namespace OAI

noncomputable section

open Matrix

open scoped BigOperators

open scoped Topology

open Filter

open Matrix

open scoped BigOperators

open Matrix MvPolynomial

open Matrix

namespace HarmonicCounterexample.Control

open scoped BigOperators

open MvPolynomial Finsupp

variable {𝕜 ι : Type*} [Field 𝕜] [Fintype ι] [DecidableEq ι]

omit [Fintype ι] in
lemma split_exponent_ne (ν : ι →₀ ℕ) (i j k : ι)
    (hn : 2 ≤ ν i) (hij : i ≠ j) (hik : i ≠ k) :
    secondExponent ν i i j k ≠ ν := by
  intro h
  have ht := congrArg (fun f : ι →₀ ℕ => f i) h
  simp only [secondExponent,Finsupp.add_apply,Finsupp.tsub_apply,Finsupp.single_apply,
    ite_eq_right hij.symm,ite_eq_right hik.symm,ite_true,zero_add] at ht
  omega

end HarmonicCounterexample.Control
end
end OAI
