@[expose] public section

noncomputable section

open Cardinal Ideal Set Pointwise

attribute [local instance 20] Classical.propDecidable

variable {T : Type*} [CommRing T] [IsLocalRing T]

lemma buildSeqSep [IsNoetherianRing T]
    (I : Ideal T)
    {C : Set (Ideal T)} (hC_prime : ∀ P ∈ C, P.IsPrime)
    (hC_ne_max : ∀ P ∈ C, P ≠ IsLocalRing.maximalIdeal T)
    (ea : ∀ P ∈ C, ∀ n, ∃ z ∈ I * IsLocalRing.maximalIdeal T ^ n, z ∉ P)
    (P_of : ℕ → Ideal T) (r_of : ℕ → T) (hP_mem : ∀ n, P_of n ∈ C) (n : ℕ) :
    ∀ m ∈ IsLocalRing.maximalIdeal T ^
        (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem (n + 1)).2,
      (buildSeq I hC_prime hC_ne_max ea P_of r_of hP_mem (n + 1)).1 + m ∉
      (P_of n : Set T) + ({r_of n} : Set T) :=
  avoidStep_sep I (P_of n) (hC_prime _ (hP_mem n)) (hC_ne_max _ (hP_mem n))
    (r_of n) (ea _ (hP_mem n)) _ _

end
end
