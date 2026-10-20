@[expose] public section

universe u v

theorem IsLocallyNormalRing.of_faithfullyFlat
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Module.FaithfullyFlat R S] [IsLocallyNormalRing S] : IsLocallyNormalRing R := by
  have stalk (p : PrimeSpectrum R) :
      IsDomain (Localization.AtPrime p.asIdeal) ∧
        IsIntegrallyClosed (Localization.AtPrime p.asIdeal) := by
    obtain ⟨q, hq⟩ :=
      (PrimeSpectrum.comap_surjective_of_faithfullyFlat (A := R) (B := S)) p
    have hpq : p.asIdeal = q.asIdeal.comap (algebraMap R S) :=
      congrArg PrimeSpectrum.asIdeal hq.symm
    let A := Localization.AtPrime p.asIdeal
    let B := Localization.AtPrime q.asIdeal
    let f : A →+* B := Localization.localRingHom p.asIdeal q.asIdeal (algebraMap R S) hpq
    let _ : Algebra A B := f.toAlgebra
    have hflat : f.Flat :=
      (RingHom.flat_algebraMap_iff.mpr (inferInstance : Module.Flat R S)).localRingHom
        q.asIdeal p.asIdeal hpq
    let _ : Module.Flat A B := hflat
    have _ : IsLocalHom (algebraMap A B) := by
      change IsLocalHom f
      exact Localization.isLocalHom_localRingHom _ _ _ hpq
    let _ : Module.FaithfullyFlat A B := Module.FaithfullyFlat.of_flat_of_isLocalHom
    have hinj : Function.Injective (algebraMap A B) := FaithfulSMul.algebraMap_injective A B
    let _ : IsDomain A := hinj.isDomain (algebraMap A B)
    refine ⟨inferInstance, (isIntegrallyClosed_iff (FractionRing A)).mpr ?_⟩
    intro x hx
    -- Map an integral fraction into the normal extension stalk.
    let φ : FractionRing A →+* FractionRing B := IsFractionRing.map hinj
    have hφ (a : A) : φ (algebraMap A (FractionRing A) a) =
        algebraMap B (FractionRing B) (algebraMap A B a) :=
      IsLocalization.map_eq _ a
    have hxB : IsIntegral B (φ x) :=
      hx.map_of_comp_eq (algebraMap A B) φ (by ext a; exact (hφ a).symm)
    obtain ⟨s, hs⟩ :=
      (isIntegrallyClosed_iff (FractionRing B)).mp (inferInstance : IsIntegrallyClosed B) hxB
    obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors A) x
    have habB : algebraMap A B a = algebraMap A B (b : A) * s := by
      apply IsFractionRing.injective B (FractionRing B)
      calc
        algebraMap B (FractionRing B) (algebraMap A B a) =
            φ (algebraMap A (FractionRing A) a) := (hφ a).symm
        _ = φ x * φ (algebraMap A (FractionRing A) (b : A)) := by
          rw [← map_mul, hab]
        _ = algebraMap B (FractionRing B) s *
            algebraMap B (FractionRing B) (algebraMap A B (b : A)) := by rw [← hs, hφ]
        _ = algebraMap B (FractionRing B) (algebraMap A B (b : A) * s) := by
          rw [map_mul, mul_comm]
    -- Faithful flatness contracts the principal ideal of the denominator.
    have haB : algebraMap A B a ∈ (Ideal.span ({(b : A)} : Set A)).map (algebraMap A B) := by
      rw [Ideal.map_span, Set.image_singleton, Ideal.mem_span_singleton]
      exact ⟨s, habB⟩
    have ha : a ∈ Ideal.span ({(b : A)} : Set A) := by
      rw [← Ideal.comap_map_eq_self_of_faithfullyFlat (B := B)
        (Ideal.span ({(b : A)} : Set A))]
      exact haB
    obtain ⟨r, hr⟩ := Ideal.mem_span_singleton.mp ha
    refine ⟨r, (IsLocalization.map_units (FractionRing A) b).mul_left_inj.mp ?_⟩
    calc
      algebraMap A (FractionRing A) r * algebraMap A (FractionRing A) (b : A) =
          algebraMap A (FractionRing A) a := by rw [← map_mul, mul_comm, ← hr]
      _ = x * algebraMap A (FractionRing A) (b : A) := hab.symm
  exact ⟨fun p ↦ (stalk p).1, fun p ↦ (stalk p).2⟩

end
