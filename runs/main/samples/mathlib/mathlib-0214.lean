@[expose] public section

open commutatorElement Subgroup

section WithGroup

variable {G : Type*} [Group G] (N : Subgroup G) [Normal N]

open Group

open QuotientGroup

section FinitePi

variable {η : Type*} {Gs : η → Type*} [∀ i, Group (Gs i)]

@[to_additive]
theorem Subgroup.lowerCentralSeries_pi_of_finite [Finite η] (Ss : ∀ i, Subgroup (Gs i)) (n : ℕ) :
    (Subgroup.pi Set.univ Ss).lowerCentralSeries n = Subgroup.pi Set.univ
      fun i => (Ss i).lowerCentralSeries n := by
  induction n with
  | zero => simp
  | succ n ih => simp_rw [lowerCentralSeries_succ, ih, commutator_pi_pi_of_finite]

end FinitePi
end WithGroup
end
