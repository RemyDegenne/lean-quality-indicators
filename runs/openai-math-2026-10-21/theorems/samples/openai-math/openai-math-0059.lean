namespace OAI

noncomputable section

namespace IntegralCharacterVarieties.SurfacePresentation.Diagram

open scoped Classical Matrix

open OccurrenceIncidence VertexTable TwoFlagBand MatrixExpression

variable {F S V R A : Type} {arity : S → ℕ} [CommRing R] [CommRing A]
    (D : Diagram F S V arity) (q : S) [Finite V]
    {r : ℕ} (d : RankShape (arity q) (arity q) r)
    (hp : D.rank (D.ports.facet ⟨q,none⟩)=r)
    (hc : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.row i))
    (hc' : ∀ i,D.rank (D.ports.facet ⟨q,some i⟩)=d.secondaryRank (.col i))
    (hproper : D.Proper) (hmax : ∀ f,D.rank f≤D.rank (D.ports.facet ⟨q,none⟩))

variable (φ : R →+* A)
    (g : (e : D.Generator) → (Matrix (Fin (D.generatorRank e)) (Fin (D.generatorRank e)) A)ˣ)
    (b0 : Fin (D.boundaryCount (D.bandCutParent q)))
    (i0 : Fin (D.boundaryLength (D.bandCutParent q) b0))
    (t a : D.FacetUnit (A:=A) (D.bandCutParent q))
    (frames : (D.refinedMarkedDiagram q d hp hc hc' hproper hmax).PortFrames (R:=A))

lemma refinedMarkedLiftSurface_inl (f : F) :
    ((D.refinedMarkedDiagram q d hp hc hc' hproper hmax).surfaceWord (.inl f)).eval φ
      (D.refinedMarkedLiftValues q d hp hc hc' hproper hmax φ g b0 i0 t a frames)=
    ((D.bandCutDiagram q).surfaceWord f).eval φ (D.bandCutLiftValues q φ g b0 i0 t a) :=
  D.refinedMarkedBandSurface_inl q d hp hc hc' hproper hmax φ frames
    (D.bandCutLiftGenerators q φ g b0 t a)
    (D.bandCutChosenJ q φ (D.bandCutLiftGenerators q φ g b0 t a) b0 i0 a)
    (D.bandCutChosenT q φ (D.bandCutLiftGenerators q φ g b0 t a) b0 i0 t)
    (D.bandCutRetainedHandles q (D.bandCutLiftGenerators q φ g b0 t a) t) f

end IntegralCharacterVarieties.SurfacePresentation.Diagram
end
end OAI
