namespace ToricIdeals.RationalNormalCurve

@[expose] public section

universe u

variable (k : Type u) [CommRing k]

theorem quotient_faithfullyFlat (n : ℕ) :
    Module.FaithfullyFlat k (Source k n ⧸ hankelIdeal k n) := by
  rcases subsingleton_or_nontrivial k with hk | hk
  · let : Subsingleton k := hk
    let : Module.FaithfullyFlat k (Unit →₀ k) :=
      Module.FaithfullyFlat.finsupp k Unit
    exact Module.FaithfullyFlat.of_linearEquiv k (Unit →₀ k)
      (Module.subsingletonEquiv k (Source k n ⧸ hankelIdeal k n) Unit)
  · let : Nontrivial k := hk
    let : Module.Free k (Source k n ⧸ hankelIdeal k n) := quotient_free k n
    let : Nontrivial (Source k n ⧸ hankelIdeal k n) :=
      (quotientAugmentation k n).toRingHom.domain_nontrivial
    infer_instance

end
end ToricIdeals.RationalNormalCurve
