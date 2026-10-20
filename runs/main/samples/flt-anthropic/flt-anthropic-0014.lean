namespace P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField

set_option autoImplicit false

open scoped TensorProduct

namespace C2idemCore

namespace IdempotentOrbit

section Core

variable {R : Type*} [CommRing R] {ι : Type*} {F : ι → Type*} [∀ i, Field (F i)]

theorem exists_idempotent_orbit_or_isField [Finite ι] (φ : R ≃+* Π i, F i) (s : R →+* R)
    {n : ℕ} (hn : n.Prime) (hs : ∀ a, (⇑s)^[n] a = a)
    {k : Type*} [Field k] (f : k →+* R) (hfix : ∀ a, s a = a → a ∈ Set.range f) :
    (∃ e : R, IsIdempotentElem e ∧ (∀ i, 0 < i → i < n → e * (⇑s)^[i] e = 0) ∧
        (∑ i ∈ Finset.range n, (⇑s)^[i] e) = 1) ∨ IsField R := by
  classical
  letI := Fintype.ofFinite ι
  rcases isEmpty_or_nonempty ι with hι | ⟨⟨j₀⟩⟩
  ·
    haveI : Subsingleton R := φ.toEquiv.subsingleton
    exact Or.inl ⟨0, Subsingleton.elim _ _, fun _ _ _ => Subsingleton.elim _ _, Subsingleton.elim _ _⟩
  haveI : Nontrivial R := ⟨⟨φ.symm 0, φ.symm 1, fun h => by
    have := congr_fun (φ.symm.injective h) j₀; simp at this⟩⟩

  have hfix01 : ∀ a : R, IsIdempotentElem a → s a = a → a = 0 ∨ a = 1 := by
    intro a ha hsa
    obtain ⟨x, rfl⟩ := hfix a hsa
    have hx : IsIdempotentElem x := by
      apply f.injective
      rw [map_mul]; exact ha
    rcases IsIdempotentElem.iff_eq_zero_or_one.mp hx with h | h
    · exact Or.inl (by rw [h, map_zero])
    · exact Or.inr (by rw [h, map_one])

  have htn : ∀ x, (⇑(conj φ s))^[n] x = x := fun x => by
    have := (semiconj_conj φ s).iterate_right n (φ.symm x)
    rw [hs, RingEquiv.apply_symm_apply] at this
    exact this.symm
  obtain ⟨ψ, hψm, hψn, hψS⟩ := exists_indexMap_of_iterate_eq (conj φ s) hn.pos htn
  obtain ⟨n', hn'⟩ : ∃ n', n = n' + 1 := ⟨n - 1, by have := hn.pos; omega⟩

  have hinv : ∀ S : Finset ι, (∀ i, ψ i ∈ S ↔ i ∈ S) → S = ∅ ∨ S = Finset.univ := by
    intro S hS
    have hfixS := hψS S hS
    have ha : s (φ.symm (ind S)) = φ.symm (ind S) := by
      apply φ.injective
      rw [← conj_apply, hfixS, RingEquiv.apply_symm_apply]
    rcases hfix01 _ ((isIdempotentElem_ind S).map φ.symm) ha with h0 | h1
    · left
      apply ind_injective (F := F)
      have := congrArg φ h0
      rwa [RingEquiv.apply_symm_apply, map_zero, ← ind_empty] at this
    · right
      apply ind_injective (F := F)
      have := congrArg φ h1
      rwa [RingEquiv.apply_symm_apply, map_one, ← ind_univ] at this

  set S : Finset ι := (Finset.range n).image fun m => ψ^[m] j₀ with hSdef
  have hmemS : ∀ m, ψ^[m] j₀ ∈ S := by
    intro m
    rw [hSdef, Finset.mem_image]
    refine ⟨m % n, Finset.mem_range.mpr (Nat.mod_lt m hn.pos), ?_⟩
    conv_rhs => rw [← Nat.mod_add_div m n, Function.iterate_add_apply, Function.iterate_mul]
    rw [Function.iterate_fixed (hψn j₀)]
  have hSinv : ∀ i, ψ i ∈ S ↔ i ∈ S := by
    intro i
    constructor
    · intro h
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp h
      have : i = ψ^[n' + m] j₀ := by
        rw [Function.iterate_add_apply, hm]
        have h2 := hψn i
        rw [hn', Function.iterate_succ_apply] at h2
        exact h2.symm
      rw [this]; exact hmemS _
    · intro h
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp h
      rw [← hm, ← Function.iterate_succ_apply' ψ m j₀]
      exact hmemS _
  have hSuniv : S = Finset.univ :=
    (hinv S hSinv).resolve_left (Finset.nonempty_iff_ne_empty.mp ⟨j₀, hmemS 0⟩)
  by_cases hfixpt : ψ j₀ = j₀
  ·
    right
    have hall : ∀ i : ι, i = j₀ := by
      intro i
      have hi : i ∈ S := hSuniv ▸ Finset.mem_univ i
      obtain ⟨m, -, hm⟩ := Finset.mem_image.mp hi
      rw [← hm]; exact Function.iterate_fixed hfixpt m
    letI : Unique ι := ⟨⟨j₀⟩, hall⟩
    exact MulEquiv.isField (Field.toIsField (F default))
      (φ.trans (RingEquiv.piUnique F)).toMulEquiv
  ·
    left
    have hper : Function.minimalPeriod ψ j₀ = n := by
      have hdvd : Function.minimalPeriod ψ j₀ ∣ n :=
        Function.IsPeriodicPt.minimalPeriod_dvd (hψn j₀)
      rcases (Nat.dvd_prime hn).mp hdvd with h1 | h2
      · exact absurd (Function.minimalPeriod_eq_one_iff_isFixedPt.mp h1) hfixpt
      · exact h2
    have hinj : Set.InjOn (fun m => ψ^[m] j₀) (Set.Iio n) :=
      hper ▸ Function.iterate_injOn_Iio_minimalPeriod
    have hne : ∀ i, 0 < i → i < n → j₀ ≠ ψ^[i] j₀ := by
      intro i hi0 hin h
      have : (0 : ℕ) = i := hinj (Set.mem_Iio.mpr hn.pos) (Set.mem_Iio.mpr hin) h
      omega
    refine ⟨φ.symm (ind {j₀}), (isIdempotentElem_ind {j₀}).map φ.symm, ?_, ?_⟩
    · intro i hi0 hin
      apply φ.injective
      rw [map_mul, map_zero, (semiconj_conj φ s).iterate_right i, RingEquiv.apply_symm_apply, hψm,
        ind_singleton_mul_ind_singleton (hne i hi0 hin)]
    · apply φ.injective
      rw [map_sum, map_one]
      simp_rw [(semiconj_conj φ s).iterate_right _ _, RingEquiv.apply_symm_apply, hψm]
      rw [← Finset.sum_image (f := fun k => (ind {k} : Π i, F i))
        (fun a ha b hb h => hinj (by simpa using ha) (by simpa using hb) h)]
      rw [← hSdef, hSuniv, ← ind_eq_sum, ind_univ]

end Core
end IdempotentOrbit
end C2idemCore
end P2MW.S_exists_isIdempotentElem_mul_iterate_eq_zero_sum_iterate_eq_one_of_not_isField
