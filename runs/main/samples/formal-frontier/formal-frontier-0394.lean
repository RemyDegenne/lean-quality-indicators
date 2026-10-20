@[expose] public section

universe u

namespace WittVector

theorem isReduced_iff {p : ℕ} [Fact p.Prime] {R : Type u} [CommRing R] :
    IsReduced (WittVector p R) ↔ IsReduced R := by
  classical
  constructor
  · intro hW
    letI : IsReduced (WittVector p R) := hW
    constructor
    intro r hr
    have ht : IsNilpotent (teichmuller p r) := by
      rcases hr with ⟨n, hn⟩
      refine ⟨n, ?_⟩
      rw [← map_pow, hn, teichmuller_zero]
    have hz : teichmuller p r = 0 := ht.eq_zero
    simpa only [teichmuller_coeff_zero, zero_coeff] using
      congrArg (fun w : WittVector p R => w.coeff 0) hz
  · intro hR
    letI : IsReduced R := hR
    have hfield : ∀ (K : Type u) [Field K], IsReduced (WittVector p K) := by
      intro K hK
      by_cases hp : (p : K) = 0
      · letI : CharP K p :=
          (CharP.charP_iff_prime_eq_zero (R := K) (Fact.out : p.Prime)).2 hp
        letI : IsDomain (WittVector p K) := inferInstance
        infer_instance
      · letI : Invertible (p : K) := invertibleOfNonzero hp
        exact isReduced_of_injective (ghostEquiv p K).toRingHom
          (ghostEquiv p K).injective
    constructor
    intro x hx
    apply WittVector.ext
    intro n
    rw [zero_coeff]
    apply IsNilpotent.eq_zero
    apply nilpotent_iff_mem_prime.mpr
    intro P hP
    letI : P.IsPrime := hP
    let f : R →+* FractionRing (R ⧸ P) :=
      (algebraMap (R ⧸ P) (FractionRing (R ⧸ P))).comp (Ideal.Quotient.mk P)
    letI : IsReduced (WittVector p (FractionRing (R ⧸ P))) :=
      hfield (FractionRing (R ⧸ P))
    have hmap : map (p := p) f x = 0 := (hx.map (map (p := p) f)).eq_zero
    have hcoeff : f (x.coeff n) = 0 := (map_eq_zero_iff f).mp hmap n
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    apply IsFractionRing.injective (R ⧸ P) (FractionRing (R ⧸ P))
    simpa only [f, RingHom.comp_apply, map_zero] using hcoeff

end WittVector
end
