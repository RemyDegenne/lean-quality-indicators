@[expose] public section

noncomputable section

lemma jensen_map_maxIdeal_eq_of_surj_closed
    (R : Subring T) [IsLocalRing ↥R]
    (h_surj : Function.Surjective (fun r : ↥R =>
      Ideal.Quotient.mk (IsLocalRing.maximalIdeal T ^ 2) (r : T)))
    (h_closed : ∀ (I : Ideal ↥R), I.FG →
      ∀ (c : ↥R), (c : T) ∈ Ideal.map R.subtype I → c ∈ I) :
    Ideal.map R.subtype (IsLocalRing.maximalIdeal ↥R) = IsLocalRing.maximalIdeal T :=
  map_maxIdeal_eq_of_surj_closed R h_surj h_closed

end
end
