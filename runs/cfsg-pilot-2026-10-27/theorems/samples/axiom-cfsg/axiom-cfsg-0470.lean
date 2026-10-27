public section

namespace CFSG.AGLEmbeddingD2.Tits.GN516.CardPar

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar

variable {K : Type*} [Group K] [Finite K] {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K}
  (hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H) (hext : SteinbergExtras D n H)

set_option hygiene false in
local notation "cs" => (coxeterMatrix D.isFiniteType).toCoxeterSystem

include hct hext in
theorem card_parJ_singleton (i : Fin D.rank) :
    Nat.card ↥(parJ D H {i}) =
      Nat.card ↥(borel D H) * (1 + Nat.card ↥(D.rootGroup (Pi.single i 1))) := by
  have hmemP : ∀ (b : ↥(borel D H)) (x : ↥(D.rootGroup (Pi.single i 1))),
      (b : K) * n i * (x : K) ∈ parJ D H {i} := fun b x =>
    mul_mem (mul_mem (borel_le_parJ _ b.2)
      (rankOne_le_parJ (Set.mem_singleton i) (hct.n_mem i)))
      (rankOne_le_parJ (Set.mem_singleton i) (Subgroup.mem_sup_left x.2))
  let f : ↥(borel D H) ⊕ (↥(borel D H) × ↥(D.rootGroup (Pi.single i 1))) →
      ↥(parJ D H {i}) :=
    Sum.elim (fun b => ⟨b.1, borel_le_parJ _ b.2⟩)
      (fun p => ⟨(p.1 : K) * n i * (p.2 : K), hmemP p.1 p.2⟩)
  have hf : Function.Bijective f := by
    refine ⟨?_, ?_⟩
    · rintro (b | ⟨b, x⟩) (b' | ⟨b', x'⟩) he
      · have he₁ := congrArg Subtype.val he
        have he₂ : (b : K) = (b' : K) := he₁
        exact congrArg Sum.inl (Subtype.ext he₂)
      · exfalso
        have hv₁ := congrArg Subtype.val he
        have hv : (b : K) = (b' : K) * n i * (x' : K) := hv₁
        apply cpNotMemBorel hct hext i
        have e : n i = (b' : K)⁻¹ * (b : K) * (x' : K)⁻¹ := by rw [hv]; group
        rw [e]
        exact mul_mem (mul_mem (inv_mem b'.2) b.2)
          (inv_mem (rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) x'.2))
      · exfalso
        have hv₁ := congrArg Subtype.val he
        have hv : (b : K) * n i * (x : K) = (b' : K) := hv₁
        apply cpNotMemBorel hct hext i
        have e : n i = (b : K)⁻¹ * (b' : K) * (x : K)⁻¹ := by rw [← hv]; group
        rw [e]
        exact mul_mem (mul_mem (inv_mem b.2) b'.2)
          (inv_mem (rootGroup_le_borel (cpSingleMem i) (ht_single_pos i) x.2))
      · have he₁ := congrArg Subtype.val he
        have he' : (b : K) * n i * (x : K) = (b' : K) * n i * (x' : K) := he₁
        obtain ⟨h1, h2⟩ := cpInj hct hext i b.2 b'.2 x.2 x'.2 he'
        rw [Subtype.ext h1, Subtype.ext h2]
    · rintro ⟨g, hg⟩
      rcases cpParJForm hct hext i hg with hgB | ⟨b, hb, x, hx, rfl⟩
      · exact ⟨Sum.inl ⟨g, hgB⟩, rfl⟩
      · exact ⟨Sum.inr (⟨b, hb⟩, ⟨x, hx⟩), rfl⟩
  have hcard := Nat.card_eq_of_bijective f hf
  rw [Nat.card_sum, Nat.card_prod] at hcard
  rw [← hcard, mul_add, mul_one]

end CFSG.AGLEmbeddingD2.Tits.GN516.CardPar
end
