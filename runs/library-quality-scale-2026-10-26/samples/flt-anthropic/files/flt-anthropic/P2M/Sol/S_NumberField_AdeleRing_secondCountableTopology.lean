import Mathlib.NumberTheory.NumberField.AdeleRing
import Mathlib.NumberTheory.NumberField.FinitePlaces
import Definitions.Def_Mathlib_LinearAlgebra_Countable
import Definitions.Def_Mathlib_Topology_Algebra_RestrictedProduct_TopologicalSpace
import P2M.Util
namespace P2MW.S_NumberField_AdeleRing_secondCountableTopology

set_option autoImplicit false

section

open scoped NumberField

open IsDedekindDomain NumberField

private scoped instance scAdele_CountableIdeal (R : Type*) [CommRing R] [Countable R] [IsNoetherianRing R] :
    Countable (Ideal R) := by
  have hsurj : Function.Surjective (fun s : Finset R => Ideal.span (s : Set R)) := by
    intro I
    obtain ⟨s, hs⟩ := IsNoetherian.noetherian I
    exact ⟨s, hs⟩
  exact hsurj.countable

private scoped instance scAdele_CountableHeightOneSpectrum (R : Type*) [CommRing R] [IsDedekindDomain R] [Countable R] :
    Countable (HeightOneSpectrum R) := by
  have hinj : Function.Injective (fun v : HeightOneSpectrum R => v.asIdeal) := fun v w h => HeightOneSpectrum.ext h
  exact hinj.countable

private scoped instance scAdele_CountableRingOfIntegers (K : Type*) [Field K] [NumberField K] : Countable (𝓞 K) :=
  Function.Injective.countable (RingOfIntegers.coe_injective (K := K))

open scoped RestrictedProduct in
private scoped instance scAdele_SecondCountableFiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (FiniteAdeleRing (𝓞 K) K) := by
  haveI : ∀ v : HeightOneSpectrum (𝓞 K), SecondCountableTopology (v.adicCompletion K) := fun v => by
    haveI : TopologicalSpace.SeparableSpace (v.adicCompletion K) :=
      ⟨_, Set.countable_range _, HeightOneSpectrum.denseRange_algebraMap (K := K) (v := v)⟩
    exact UniformSpace.secondCountable_of_separable _
  haveI : SecondCountableTopology
      (Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]) :=
    RestrictedProduct.secondCountableTopology fun v => Valued.isOpen_valuationSubring _
  exact inferInstanceAs <| SecondCountableTopology <|
    Πʳ v : HeightOneSpectrum (𝓞 K), [v.adicCompletion K, v.adicCompletionIntegers K]

private scoped instance scAdele_SecondCountableInfiniteAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (InfiniteAdeleRing K) := by
  haveI : ∀ v : NumberField.InfinitePlace K, SecondCountableTopology v.Completion := by
    intro v
    haveI : Countable (WithAbs v.1) := (WithAbs.equiv v.1).toEquiv.injective.countable
    haveI : SecondCountableTopology v.1.Completion := UniformSpace.secondCountable_of_separable _
    exact (NumberField.InfinitePlace.Completion.isometryEquivCompletion v).toHomeomorph.secondCountableTopology
  exact inferInstanceAs <| SecondCountableTopology <| (v : NumberField.InfinitePlace K) → v.Completion

private scoped instance scAdele_SecondCountableAdeleRing (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (AdeleRing (𝓞 K) K) :=
  inferInstanceAs <| SecondCountableTopology (InfiniteAdeleRing K × FiniteAdeleRing (𝓞 K) K)

end

theorem solution (K : Type*) [Field K] [NumberField K] :
    SecondCountableTopology (NumberField.AdeleRing (NumberField.RingOfIntegers K) K) :=
  inferInstance
