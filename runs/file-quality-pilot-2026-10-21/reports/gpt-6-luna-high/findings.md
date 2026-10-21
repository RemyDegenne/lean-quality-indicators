# Findings

### statement-generality: [Mathlib/RingTheory/TensorProduct/Free.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/RingTheory/TensorProduct/Free.lean#L109-L113)

Declaration: `Algebra.TensorProduct.instFree`

The instance requires A to be commutative, although the basis used to prove freeness only requires A to be a semiring. This excludes base changes to noncommutative algebras despite the same proof applying.

Proposed change:

Replace `[CommSemiring A]` with `[Semiring A]` in the instance assumptions, retaining `[Algebra R A]`. The existing proof via `Module.Free.of_basis` applied to `Algebra.TensorProduct.basis A (Module.Free.chooseBasis R M)` works with those assumptions.

Benefit: Makes the freeness result available for base change to noncommutative semirings, without changing the result for commutative A. The empty-basis case is unchanged: the construction still supplies a basis when M is zero.

Source evidence:

- `Algebra.TensorProduct.basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/RingTheory/TensorProduct/Free.lean`: variable [CommSemiring R] [Semiring A] [Algebra R A]
- `Module.Free.of_basis` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/FreeModule/Basic.lean`: variable [Semiring R] [AddCommMonoid M] [Module R M]

### statement-generality: [Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L351-L352)

Declaration: `CliffordAlgebra.equivExterior`

The statement requires 2 to be invertible in R even when the particular quadratic form Q admits a bilinear form B with B.toQuadraticMap = 0 - Q. In that case the existing changeFormEquiv construction already supplies the module isomorphism, without requiring invertibility of 2. The file’s own documentation acknowledges the broader case of Q divisible by two.

Proposed change:

Add a general version accepting a witness, for example `def equivExteriorOfBilin (B : BilinForm R M) (h : B.toQuadraticMap = 0 - Q) : CliffordAlgebra Q ≃ₗ[R] ExteriorAlgebra R M := changeFormEquiv h`. The current `equivExterior` can remain as a convenient specialization using `changeForm.associated_neg_proof`. For Q = 2 • Q₀, such a witness is `-QuadraticMap.polarBilin Q₀`, since `QuadraticMap.toQuadraticMap_polarBilin` gives the diagonal 2 • Q₀.

Benefit: Users can obtain the Clifford-to-exterior module isomorphism for quadratic forms divisible by two even when 2 is not invertible, including degenerate cases. The proof reuses the existing `changeFormEquiv` and the bilinear witness; it does not rely on division by two.

Source evidence:

- `CliffordAlgebra.equivExterior` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: Note that this holds more generally when `Q` is divisible by two, rather than only when `1` is
divisible by two; but that would be more awkward to use.
- `CliffordAlgebra.changeFormEquiv` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`: def changeFormEquiv : CliffordAlgebra Q ≃ₗ[R] CliffordAlgebra Q' :=
  { changeForm h with
- `QuadraticMap.toQuadraticMap_polarBilin` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/QuadraticForm/Basic.lean`: theorem _root_.QuadraticMap.toQuadraticMap_polarBilin (Q : QuadraticMap R M N) :
    toQuadraticMap (polarBilin Q) = 2 • Q

### statement-generality: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L352-L355)

Declaration: `TauCeti.exists_isSolidTorusNeighborhood`

The conclusion is stated only for `ℝ³ := EuclideanSpace ℝ (Fin 3)`, although the geometric argument needs a three-dimensional real inner product space, not this specific model. The file's tubular-neighborhood theorem already supports general finite-dimensional real inner product spaces.

Proposed change:

Generalize the theorem to `{V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]` with `hV : Module.finrank ℝ V = 3`, replacing the occurrences of `ℝ³` in its inputs and conclusion by `V`. Transport `f` and `U` along a linear isometry `V ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 3)`, apply the existing result, then transport the resulting framing back. The dimension hypothesis ensures the transported ambient space has the needed three-dimensional geometry; in particular, it avoids claiming this solid-torus conclusion in dimensions where the normal plane is not two-dimensional.

Benefit: Users working with any three-dimensional real inner product space can apply the existence result directly, without first choosing coordinates or converting their embedding and neighborhood to the library's specific `EuclideanSpace` model.

Source evidence:

- `TauCeti.exists_isSolidTorusNeighborhood` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: theorem exists_isSolidTorusNeighborhood {f : Circle → ℝ³} (hf : ContMDiff (𝓡 1) 𝓘(ℝ, ℝ³) 2 f)
- `TauCeti.exists_isOpenEmbedding_normalTube` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Geometry/Manifold/TubularNeighborhood/Euclidean.lean`: variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

### statement-generality: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L53-L75)

Declaration: `clm_decompose and clm_indicator'_eq_additiveFunction`

Both helper statements require a continuous linear map, but their proofs only use linearity (`map_smul` and `map_sum`) to evaluate finite sums. Continuity is not needed for these identities, so the statements are unnecessarily specialized.

Proposed change:

Change the argument in both declarations at lines 53–54 and 71–72 from `(Λ : (U → ℝ) →L[ℝ] ℝ)` to `(Λ : (U → ℝ) →ₗ[ℝ] ℝ)`. Their existing proofs use linear-map operations. At the later calls where the separating functional is a continuous linear map, pass `Λ.toLinearMap` if elaboration does not insert the coercion.

Benefit: The identities become reusable for any linear functional, including where no topology or continuity structure is available. This preserves the finite-sum mathematics and does not change the Hahn–Banach argument, which still uses a continuous linear map.

Source evidence:

- `clm_decompose` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: rw [this, map_smul, smul_eq_mul]
- `clm_decompose` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: _ = ∑ i, Λ (Function.update (0 : U → ℝ) i (h i)) := map_sum Λ _ _
- `additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/Defs.lean`: fun A => ∑ i ∈ A, a i

### statement-generality: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L95-L99)

Declaration: `fourier_postcompCLM`

The theorem is generic in its value spaces and postcomposition map, but fixes the Fourier domain to `L2Vec3`. Mathlib’s Schwartz Fourier API is stated for any finite-dimensional real inner-product domain, so this useful postcomposition identity is unnecessarily restricted to the library’s 3D coordinates.

Proposed change:

Replace the fixed domain with a variable `V` carrying `[NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]`, and change `SchwartzMap L2Vec3 F` to `SchwartzMap V F`. The proof can use the same `Real.fourier_eq` rewrites and `L.integral_comp_comm` argument. This formulation includes the zero-dimensional case; no nonzero-dimension assumption is needed for the integral-commutation argument.

Benefit: The identity becomes reusable for Schwartz Fourier transforms on other finite-dimensional real inner-product spaces, without duplicating its proof for each spatial domain.

Source evidence:

- `fourier_postcompCLM` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: (L : F →L[ℂ] G) (f : SchwartzMap L2Vec3 F) :
- `SchwartzMap Fourier variables` in `/tmp/nix-shell.1apE0t/luna-file-audit-runtime-gr27_q3q/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Distribution/SchwartzSpace/Fourier.lean`: {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]
  [MeasurableSpace V] [BorelSpace V]

### statement-generality: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L154-L159)

Declaration: `sectorCurve_norm_on_arc`

The arc’s modulus is stated as `r` only under the positivity assumption. For any real `r`, including zero and negative values, its modulus is `|r|`; the arc formula itself does not require positivity.

Proposed change:

State `theorem sectorCurve_norm_on_arc (r : ℝ) (α : ℝ) (t : ℝ) (ht : t ∈ Icc 1 2) : ‖sectorCurve r α t‖ = |r|`. The proof can rewrite with `sectorCurve_seg2` and use the norm of a product and `Complex.norm_exp_I_mul_ofReal`; the real scalar factor contributes `|r|`.

Benefit: This gives the actual modulus formula without restricting the radius parameter to positive reals, including the degenerate case `r = 0`, and makes the geometric fact usable for signed parameters.

Source evidence:

- `sectorCurve_norm_on_arc` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: rw [sectorCurve_seg2 r α t ht]
  simp only [norm_mul, Complex.norm_exp_I_mul_ofReal, mul_one]
  exact Complex.norm_of_nonneg (le_of_lt hr)

### statement-generality: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L387-L393)

Declaration: `parabolicRieszKernel_tail_le (with matching weakening in its helper lemmas)`

The estimate is restricted to q ≥ 1, although the Morrey cell and norm are defined for real q, and the inspected proof uses this lower bound only to obtain q > 0 (and, in the scale identity, to establish an unused nonnegativity fact). The estimates therefore need not exclude positive q below 1.

Proposed change:

Replace the q hypothesis with `hq : 0 < q` in `parabolicRieszKernel_tail_le` and the corresponding helper signatures (`cylinderAbsIntegral_le_morreyNorm`, `positive_shell_integral_le`, and `positive_shell_scale_identity`). In the scale-identity proof, use hq directly for q positivity and remove or replace the auxiliary `hα` proof, which is not used later. The cylinder integral estimate still follows from the Morrey supremum bound and cancellation of the radius powers; the shell estimate uses that cylinder estimate, while `ennreal_mul_rpow` already handles either sign of its exponent. The dyadic decay condition `β * q < 5` remains in place.

Benefit: This admits the same tail bound for positive q < 1, extending its use to quasi-Morrey parameters without changing the geometry or the stated estimate. The positive-q condition also preserves the meaningful division by q; no q = 0 case is introduced.

Source evidence:

- `parabolicRieszKernel_tail_le` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: (hq : 1 ≤ q) (hβq : β * q < 5)
- `cylinderAbsIntegral_le_morreyNorm` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: (hq : 1 ≤ q)
- `positive_shell_scale_identity` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: have hα : 0 ≤ α := by
- `morreyNorm` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Basic.lean`: def morreyNorm (p q : ℝ) (f : ParabolicPoint → ℝ) : ℝ≥0∞ :=

### statement-generality: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L37-L43)

Declaration: ``RS.taylorCoeffAt` and the downstream declarations in the namespace, especially `AnalyticAt.exists_taylor_remainder``

The coefficient extractor and its analytic-germ results are specialized throughout to complex-valued functions, although the `dslope` iteration and the power-series iteration used by the proofs are available over any nontrivially normed field. This unnecessarily restricts use of the coefficient and remainder results to ℂ.

Proposed change:

Parameterize the namespace declarations by `{𝕜 : Type*} [NontriviallyNormedField 𝕜]`, use functions `𝕜 → 𝕜` and base point `z₀ : 𝕜`, and replace the occurrences of `ℂ` in the declarations and hypotheses with `𝕜`. For example, state `taylorCoeffAt (g : 𝕜 → 𝕜) (z₀ : 𝕜) (j : ℕ) : 𝕜`, and state the remainder theorem with `AnalyticAt 𝕜 g z₀`. The `NontriviallyNormedField` assumption is important: it matches the `dslope` interface rather than claiming the result for the degenerate trivial field.

Benefit: Users working over other nontrivially normed fields can use the same coefficient, shift, and exact analytic remainder results without translating them to ℂ. The proof dependencies support this generalization: the iterated `dslope` power-series lemma and the multiplication derivative lemma are already stated generically, while the displayed proof steps use field operations and algebraic identities rather than complex-specific facts.

Source evidence:

- ``RS.taylorCoeffAt` namespace variable block` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: variable {f g F : ℂ → ℂ} {z₀ : ℂ}

/-- The `j`-th Taylor coefficient
- ``dslope`` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/DSlope.lean`: variable {𝕜 E : Type*} [NontriviallyNormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E]
- ``HasFPowerSeriesAt.has_fpower_series_iterate_dslope_fslope`` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Analytic/IsolatedZeros.lean`: theorem has_fpower_series_iterate_dslope_fslope (n : ℕ) (hp : HasFPowerSeriesAt f p z₀) :
    HasFPowerSeriesAt ((swap dslope z₀)^[n] f) (fslope^[n] p) z₀ := by
- ``deriv_const_mul_field`` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Analysis/Calculus/Deriv/Mul.lean`: theorem deriv_const_mul_field (u : 𝕜') : deriv (fun y => u * v y) x = u * deriv v x := by

### statement-generality: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L56-L61)

Declaration: `LimitRepresentation.smoothPeriodicTest_memL2On`

The conclusion that a function is square-integrable on the unit cube uses only continuity, not smoothness. The compact-cell argument integrates the square of a continuous function, so requiring all derivatives unnecessarily excludes continuous tests from this helper.

Proposed change:

Weaken the hypothesis to `(hψ : Continuous ψ)`. The existing proof can use `hψ.measurable.aestronglyMeasurable` in the `memLp_two_iff_integrable_sq` step and `(hψ.pow 2).continuousOn.integrableOn_compact` in the compactness step, retaining the same closed-cell compactness and subset arguments. This weakening includes degenerate cases such as the zero function without additional assumptions. The downstream `smoothPeriodicTestL2` can retain its `ContDiff` interface if smoothness is needed there.

Benefit: Makes the integrability result available to continuous tests without asking callers to provide irrelevant differentiability evidence, while preserving the same conclusion and proof strategy.

Source evidence:

- `LimitRepresentation.smoothPeriodicTest_memL2On` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: (hψ : ContDiff ℝ (⊤ : ℕ∞) ψ) : MemL2On AVenhance.unitCube ψ := by
- `LimitRepresentation.representationClosedCell_compact` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: LimitRepresentation.representationClosedCell_compact |>.mono_set
        LimitRepresentation.unitCube_subset_representationClosedCell

### statement-generality: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L45-L48)

Declaration: `planeCurveToBivariate`

This coordinate-presentation equivalence requires only a commutative semiring of coefficients, but its signature requires a field. The adjacent generator and constant identities and the outer-degree identity (lines 51–113) are likewise structural and can use the weaker assumption.

Proposed change:

Change the coefficient assumption on `planeCurveToBivariate` to `[CommSemiring K]`; generalize the adjacent `planeCurveToBivariate_X_zero`, `planeCurveToBivariate_X_one`, `planeCurveToBivariate_C`, and `planeCurveToBivariate_natDegree_eq_degreeOf_zero` statements to the same assumption. Their proofs use the polynomial equivalences and degree correspondence, not division or field properties. The zero-polynomial case remains covered by the existing nat-degree correspondence.

Benefit: Users can reuse the coordinate conversion and its basic degree facts for polynomial rings over commutative semirings, including rings with zero divisors, without adding an artificial field structure.

Source evidence:

- `planeCurveToBivariate` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`: def planeCurveToBivariate (K : Type*) [Field K] :
    MvPolynomial (Fin 2) K ≃ₐ[K] Polynomial (Polynomial K) :=
- `MvPolynomial.finSuccEquiv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/MvPolynomial/Equiv.lean`: def finSuccEquiv : MvPolynomial (Fin (n + 1)) R ≃ₐ[R] Polynomial (MvPolynomial (Fin n) R) :=
- `MvPolynomial.natDegree_finSuccEquiv` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/MvPolynomial/Equiv.lean`: theorem natDegree_finSuccEquiv (f : MvPolynomial (Fin (n + 1)) R) :
    (finSuccEquiv R n f).natDegree = degreeOf 0 f := by
  by_cases c : f = 0

### statement-generality: [LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L76-L88)

Declaration: `localL2Energy_ball_le_of_ae_bound`

The pointwise-bound argument is restricted to balls centered at zero, although its integral comparison does not use the ball geometry; geometry is needed only afterward to evaluate the ball's volume. This prevents users from applying the same estimate directly to other finite-measure measurable regions.

Proposed change:

Add a general theorem, retaining this ball theorem as a corollary: `theorem localL2Energy_le_of_ae_bound (s : Set Space) (u : L2) (C : ℝ) (hs : MeasurableSet s) (hfinite : volume s ≠ ∞) (hbound : ∀ᵐ x ∂volume, x ∈ s → ‖u x‖ ^ 2 ≤ C) : localL2Energy s u ≤ (volume s).toReal * C`. Its proof follows the existing integral comparison, using `(integrable_norm_sq_L2 u).integrableOn`, `integrableOn_const hfinite`, and `(ae_restrict_iff' hs).2 hbound`; evaluate the constant integral with `setIntegral_const` and `smul_eq_mul`. Recover the current ball result using `Metric.isOpen_ball.measurableSet`, `measure_ball_lt_top.ne`, and `volume_ball_toReal r hr`. This formulation also handles radius zero and needs no extra nonnegativity assumption on C: the stated almost-everywhere bound remains the premise in degenerate cases.

Benefit: Users can bound local energy on any measurable finite-volume region without reproving the same measure-theoretic comparison, while the existing explicit three-dimensional ball estimate remains available.

Source evidence:

- `localL2Energy_ball_le_of_ae_bound` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean`: apply integral_mono_ae (integrable_norm_sq_L2 u).integrableOn
        (integrableOn_const (measure_ball_lt_top.ne))
- `integrableOn_const` in `/tmp/nix-shell.1apE0t/luna-file-audit-runtime-gr27_q3q/repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/IntegrableOn.lean`: theorem integrableOn_const {C : ε'} (hs : μ s ≠ ∞ := by finiteness)
- `setIntegral_const` in `/tmp/nix-shell.1apE0t/luna-file-audit-runtime-gr27_q3q/repos/deps/mathlib-c55e6e786f49/Mathlib/MeasureTheory/Integral/Bochner/Set.lean`: theorem setIntegral_const [CompleteSpace E] (c : E) : ∫ _ in s, c ∂μ = μ.real s • c := by

### vacuity-and-misstatement: [Mathlib/Control/Traversable/Equiv.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Control/Traversable/Equiv.lean#L94-L96)

Declaration: `Equiv.traverse (documentation)`

The description identifies `t'` as the traversable source, but the declaration requires `[Traversable t]` and computes traversal by applying `traverse` to `(eqv α).symm x`, an element of `t α`. Thus the documentation gives readers the wrong functor whose traversability must be available.

Proposed change:

Replace “using a traversable functor `t'`” with “using a traversable functor `t`.”

Benefit: Readers can identify the required source instance and understand that the equivalences transfer its traversal structure to `t'`.

Source evidence:

- `Equiv.traverse` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Control/Traversable/Equiv.lean`: variable [Traversable t]
variable {m : Type u → Type u} [Applicative m]
- `Equiv.traverse` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Control/Traversable/Equiv.lean`: eqv β <$> traverse f ((eqv α).symm x)
- `Traversable` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Control/Traversable/Basic.lean`: class Traversable (t : Type u → Type u) extends Functor t where
  /-- The function commuting a traversable functor `t` with an arbitrary applicative functor `m`. -/
  traverse

### vacuity-and-misstatement: [TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean#L89-L91)

Declaration: `TauCeti.NumberField.FifthCyclotomic.isMonogenic`

The docstring claims the specific equality `𝓞 K = ℤ[ζ₅]`, but the declaration concludes only `IsMonogenic K`, which is existential: some integral element generates the ring of integers. Thus users of this theorem cannot obtain the claimed canonical-generator equality from its conclusion.

Proposed change:

Either weaken the docstring to say only that the field is monogenic, or add a separate theorem whose conclusion explicitly states that the adjoin of the canonical primitive fifth root (or its integral lift) is `⊤`, and retain the stronger wording only for that theorem.

Benefit: Aligns the documented result with its usable conclusion and makes the specific cyclotomic generator available to downstream users when that is the intended result.

Source evidence:

- `TauCeti.NumberField.FifthCyclotomic.isMonogenic` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean`: /-- A fifth cyclotomic field is monogenic: `𝓞 K = ℤ[ζ₅]`. -/
theorem isMonogenic : IsMonogenic K :=
- `TauCeti.NumberField.IsMonogenic` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/NumberTheory/NumberField/Monogenic.lean`: def IsMonogenic (K : Type*) [Field K] : Prop :=
  ∃ θ : 𝓞 K, Algebra.adjoin ℤ {θ} = ⊤

### simp-interface: [Mathlib/Data/DFinsupp/Interval.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Data/DFinsupp/Interval.lean#L88-L89)

Declaration: `DFinsupp.mem_singleton_apply_iff`

The theorem gives the expected normal form for membership in the pointwise singleton, but is not tagged `[simp]`. Thus the direct expression `a ∈ f.singleton i` does not have this rule available to `simp`, even though the underlying Finset membership rule is a simp lemma.

Proposed change:

Add `@[simp]` to `mem_singleton_apply_iff`, so `simp` rewrites `a ∈ f.singleton i` to `a = f i`.

Benefit: Users can discharge or normalize membership goals involving the bundled singleton with the standard simplifier, consistently with `Finset.mem_singleton`.

Source evidence:

- `DFinsupp.mem_singleton_apply_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/DFinsupp/Interval.lean`: theorem mem_singleton_apply_iff : a ∈ f.singleton i ↔ a = f i :=
  mem_singleton
- `Finset.mem_singleton` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Data/Finset/Insert.lean`: @[simp, grind =]
theorem mem_singleton {a b : α} : b ∈ ({a} : Finset α) ↔ b = a :=

### simp-interface: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L268-L274)

Declaration: `Bundle.Trivialization.coordChangeL`

There is no simp rule reducing a trivialization's coordinate change with itself to the identity. On the overlap, the definition composes a linear equivalence with its inverse; outside the overlap, it already chooses the identity. The absence of a generic rule leaves even this canonical self-change unreduced.

Proposed change:

Add a theorem such as `@[simp] theorem coordChangeL_self (e : Trivialization F (π F E)) [e.IsLinear R] (b : B) : e.coordChangeL R e b = ContinuousLinearEquiv.refl R F := ...`. This gives `(e.coordChangeL R e b) v` the normal form `v`; it could also replace the special-case identity theorem for the trivial bundle.

Benefit: Users can simplify redundant self-coordinate changes directly, without unfolding the conditional definition or proving a chart-specific identity. This is a terminating reduction to the identity and matches the existing trivial-bundle use.

Source evidence:

- `Bundle.Trivialization.coordChangeL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: then (e.linearEquivAt R b (hb.1 :)).symm.trans (e'.linearEquivAt R b hb.2)
      else LinearEquiv.refl R F
- `trivialization.coordChangeL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Constructions.lean`: theorem trivialization.coordChangeL (b : B) :
    (trivialization B F).coordChangeL 𝕜 (trivialization B F) b =
      ContinuousLinearEquiv.refl 𝕜 F := by

### simp-interface: [Mathlib/Control/Traversable/Equiv.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Control/Traversable/Equiv.lean#L126-L127)

Declaration: `Equiv.id_traverse`

The transferred identity-traverse law is not a simp lemma. Consequently, simplifying the natural identity traversal expression for `t'` does not use this law unless callers explicitly name `Equiv.id_traverse`. This is especially relevant because `Equiv.traversable eqv` is explicitly constructed rather than installed as an instance, so generic simp access through a synthesized `LawfulTraversable t'` is not assured.

Proposed change:

Mark `Equiv.id_traverse` with `@[simp]`, so `simp` can reduce `Equiv.traverse eqv (pure : α → Id α) x` to `pure x` directly.

Benefit: Makes the transferred law available to ordinary simplification, matching the existing simp treatment of the generic lawful traversable identity law, without expanding `Equiv.traverse` or changing its orientation.

Source evidence:

- `Equiv.id_traverse` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Control/Traversable/Equiv.lean`: protected theorem id_traverse (x : t' α) : Equiv.traverse eqv (pure : α → Id α) x = pure x := by
- `LawfulTraversable.id_traverse simp attribute` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Control/Traversable/Lemmas.lean`: attribute [simp] LawfulTraversable.id_traverse

### simp-interface: [Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean#L53-L56)

Declaration: `ZMod.toCircle_intCast`

This cast-to-exponential formula is not a simp lemma, so routine expressions such as `ZMod.toCircle (j : ZMod N)` do not simplify to the explicit character value unless callers name the theorem. The neighboring `stdAddChar_coe` proof has to include `toCircle_intCast` explicitly, while an analogous `AddChar.zmod_intCast` formula in the Pontryagin duality source is marked `[simp]`.

Proposed change:

Consider marking `toCircle_intCast` with `@[simp]`, so `simp` normalizes `ZMod.toCircle (j : ZMod N)` to `exp (2 * π * I * j / N)`. Check the resulting simp behavior alongside `toCircle_natCast` before also annotating the natural-cast variant.

Benefit: Makes the explicit value available through ordinary simplification for integer-cast inputs and aligns this API with the analogous character formula. This can reduce manual theorem references in proofs while retaining the exponential expression as the normal form.

Source evidence:

- `ZMod.toCircle_intCast` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: lemma toCircle_intCast (j : ℤ) :
    toCircle (j : ZMod N) = exp (2 * π * I * j / N) := by
- `ZMod.stdAddChar_coe` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Complex/CircleAddChar.lean`: stdAddChar (j : ZMod N) = exp (2 * π * I * j / N) := by simp [stdAddChar, toCircle_intCast]
- `AddChar.zmod_intCast` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/Fourier/FiniteAbelian/PontryaginDuality.lean`: @[simp] lemma zmod_intCast (x y : ℤ) : zmod n x y = exp (2 * π * (x * y / n)) := by

### simp-interface: [TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean#L221-L225)

Declaration: `tangentVector_circleExp`

This provides the canonical simplification of the velocity at an exponential-parametrized point, but is not in the simp set. The file consequently invokes it manually at two later uses.

Proposed change:

Add the `[simp]` attribute to `tangentVector_circleExp`, keeping its current left-to-right orientation so `tangentVector f (Circle.exp t)` simplifies to the derivative expression.

Benefit: The normal form is the derivative already used in the proofs, and simp can perform the conversion at the existing occurrences without explicit rewrites. The proposed direction does not unfold the derivative back into the definition of `tangentVector`.

Source evidence:

- `tangentVector_circleExp` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: tangentVector f (Circle.exp t) = deriv (f ∘ Circle.exp) t
- `tangentVector_ne_zero_and_mem_normalSubspace_iff` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: rw [tangentVector_circleExp]
- `exists_forall_notMem_span_tangentVector` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/LowDimTopology/SolidTorusNeighborhood/Basic.lean`: rw [tangentVector_circleExp] at hz

### simp-interface: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L71-L75)

Declaration: `clm_indicator'_eq_additiveFunction`

This useful normalization is not in the simp set. The file has to invoke it manually when reasoning about a continuous linear map applied to an indicator: it constructs the equality with `convert` at lines 155–156 and rewrites with the lemma at lines 162–163. Thus ordinary `simp` does not normalize `Λ S.indicator'` to the additive function of the basis evaluations.

Proposed change:

Add `@[simp]` to `clm_indicator'_eq_additiveFunction`, keeping its current orientation. The desired normal form is `additiveFunction (fun i => Λ (Function.update 0 i 1)) S` for `Λ S.indicator'`. This rewrite removes the indicator application rather than recreating it, so it does not introduce an evident rewrite cycle. It also applies in the empty-finset case, where the additive function is the empty sum.

Benefit: Users can simplify linear-map applications to indicators directly and avoid repeated explicit `convert`/`rw` steps, as already needed in this proof.

Source evidence:

- `clm_indicator'_eq_additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: lemma clm_indicator'_eq_additiveFunction (Λ : (U → ℝ) →L[ℝ] ℝ) (S : Finset U) :
    Λ S.indicator' = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by
- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: have hΛ_S : Λ (S.indicator') = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by
      convert clm_indicator'_eq_additiveFunction Λ S using 1;
- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: have h_additiveFunction_a_neg : additiveFunction a S = -Λ (S.indicator') := by
      rw [ clm_indicator'_eq_additiveFunction Λ S ]; ring_nf!;

### simp-interface: [LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean#L147-L150)

Declaration: `weakTestGradientSchwartz_apply`

This establishes a useful canonical component normal form for the exposed `weakTestGradientSchwartz` definition, but the theorem is private and is not tagged `[simp]`. Consequently downstream users cannot use this normal form to simplify component expressions; unfolding the definition instead exposes the derivative, postcomposition, and coordinate-equivalence implementation. The file itself uses the equation in a componentwise proof.

Proposed change:

Make this equation public and tag it `[simp]`, preserving the stated orientation: `weakTestGradientSchwartz ψ x i` simplifies to `(ψ.partialDeriv i (l2Vec3Equiv x) : ℂ)`.

Benefit: Users of the exposed gradient encoding can obtain the coordinate derivative as a stable, concise normal form without unfolding its construction. The rule reduces an application to the mathematical quantity it represents and does not expand that quantity back into the implementation.

Source evidence:

- `weakTestGradientSchwartz` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: def weakTestGradientSchwartz
    (ψ : WeakTestFunction (Set.univ : Set Vec3)) :
    SchwartzMap L2Vec3 ComplexVec3 :=
- `realPart_isWeakDivFree_of_fourierOrthogonal` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Leray/FourierPhysicalRange.lean`: weakTestGradientSchwartz_apply,
      RCLike.inner_apply

### simp-interface: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L74-L83)

Declaration: `sectorCurve_zero and sectorCurve_three`

These canonical endpoint evaluations are not simp lemmas. A downstream proof must name both explicitly to simplify the endpoint values, even though their right-hand sides are terminal values and rewriting them cannot expand the curve or create a rewrite cycle.

Proposed change:

Add `@[simp]` to `sectorCurve_zero` and `sectorCurve_three` so ordinary `simp` calls normalize these endpoint evaluations.

Benefit: Downstream endpoint calculations can use the standard simplifier instead of repeatedly listing these theorems, while preserving the endpoint values and behavior at degenerate parameter choices.

Source evidence:

- `sectorCurve_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: theorem sectorCurve_zero (r : ℝ) (α : ℝ) :
    sectorCurve r α 0 = 0 := by simp [sectorCurve]
- `sectorCurve_three` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: theorem sectorCurve_three (r : ℝ) (α : ℝ) :
    sectorCurve r α 3 = 0 := by
- `pv_sector_higher_power` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurveLemma.lean`: simp only [F, sectorCurve_zero, sectorCurve_three, zero_pow (by omega : n ≠ 0),

### simp-interface: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L97-L103)

Declaration: `RS.taylorCoeffAt_const_mul`

The theorem gives a canonical simplification for coefficients of constant scalar multiples, but is not tagged `[simp]`. As a result, ordinary `simp` does not normalize expressions such as `taylorCoeffAt (fun z => c * f z) z₀ k`; callers must invoke the theorem explicitly.

Proposed change:

Add `@[simp]` to `taylorCoeffAt_const_mul`, retaining the orientation from the coefficient of the scalar-multiplied function to scalar multiplication of the coefficient.

Benefit: This gives scalar-multiple coefficients the same automatic normalization available for constants and monomials, and removes explicit rewrites at existing uses without expanding the coefficient definition.

Source evidence:

- `RS.taylorCoeffAt_const_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: theorem taylorCoeffAt_const_mul (c : ℂ) (j : ℕ) :
    taylorCoeffAt (fun z => c * g z) z₀ j = c * taylorCoeffAt g z₀ j := by
- `RS.laurentCoeffAt_const_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/LaurentCoeff.lean`: · rw [taylorCoeffAt_const_mul]

### simp-interface: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L149-L151)

Declaration: `weakPathRepresentative`

When time is already supplied as an element of the closed interval, the canonical simplification to the corresponding torus representative is not exposed as a simp rule. This file repeats a function-extensionality proof that unfolds the definition and uses the interval membership proof at lines 171–175, 180–184, and 200–205. The desired normal form is `scalarTorusRepresentative (u t)` for `weakPathRepresentative u (t : ℝ)` with `t : Icc (0 : ℝ) 1`.

Proposed change:

Add a directed simp lemma such as `@[simp] theorem weakPathRepresentative_coe (u : Icc (0 : ℝ) 1 → ScalarTorusL2) (t : Icc (0 : ℝ) 1) : weakPathRepresentative u (t : ℝ) = scalarTorusRepresentative (u t) := by simp [weakPathRepresentative]`. This rewrites only the interval-subtype case and removes the `if` using `t.property`; its right-hand side does not introduce `weakPathRepresentative`, so it does not create a rewrite cycle.

Benefit: The existing proofs and downstream users can simplify the representative directly, avoiding repeated extensionality and unfolding while keeping the zero-outside-the-interval behavior unchanged.

Source evidence:

- `weakPathRepresentative_memL2On` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: have hfun : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by
    funext x
    simp [weakPathRepresentative, t.property]
- `weakPathRepresentative_l2NormSq` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: have hfun : weakPathRepresentative u t = scalarTorusRepresentative (u t) := by
    funext x
    simp [weakPathRepresentative, t.property]
- `fromUnitTorus` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: def fromUnitTorus {d : ℕ} {α : Type*}
    (f : UnitAddTorus (Fin d) → α) : Vec d → α :=
  fun x => f (toUnitTorus d x)

### simp-interface: [LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean#L35-L36)

Declaration: `integral_norm_sq_L2`

This is a canonical whole-space integral-to-norm simplification, but it is not tagged `[simp]`. A downstream proof must explicitly name the theorem to normalize this expression.

Proposed change:

Add `@[simp]` to `integral_norm_sq_L2`, retaining its current orientation so that `∫ x, ‖u x‖ ^ 2` simplifies to `‖u‖ ^ 2`.

Benefit: The rule gives the whole-space integral a compact canonical normal form and lets downstream simplification use the identity without repeatedly spelling out a rewrite. For example, `localized_coefficient_lower` currently explicitly rewrites by this theorem.

Source evidence:

- `integral_norm_sq_L2` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/NavierStokesAndEuler/Euler/MeanLocalL2Energy.lean`: theorem integral_norm_sq_L2 (u : L2) : (∫ x, ‖u x‖ ^ 2) = ‖u‖ ^ 2 := by
- `localized_coefficient_lower` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/NavierStokesAndEuler/Euler/MeanSourceVariationalInverse.lean`: integral_const_mul, integral_const_mul, integral_indicator hs, integral_norm_sq_L2]

### readable-proof-simplification: [Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean#L60-L61)

Declaration: `CategoryTheory.Functor.IsWellOrderContinuous instance for ℕ`

The proof relies on `simp` to discover that `hm` is impossible, leaving the reason this instance is vacuous implicit. The adjacent Fin instance uses a named order-theory result for the same fact.

Proposed change:

Replace the proof with `nonempty_isColimit m hm := (Order.not_isSuccLimit_of_isSuccArchimedean hm).elim`.

Benefit: The named lemma makes the key mathematical reason explicit: an Archimedean successor order has no successor-limit elements. This is at least as easy to follow as asking `simp` to close the goal, and aligns the ℕ proof with the neighboring Fin proof.

Source evidence:

- `CategoryTheory.Functor.IsWellOrderContinuous instance for ℕ` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean`: nonempty_isColimit m hm := by simp at hm
- `CategoryTheory.Functor.IsWellOrderContinuous instance for Fin n` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/CategoryTheory/Limits/Shapes/Preorder/WellOrderContinuous.lean`: nonempty_isColimit _ hj := (Order.not_isSuccLimit_of_isSuccArchimedean hj).elim
- `Order.not_isSuccLimit_of_isSuccArchimedean` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Limit.lean`: theorem not_isSuccLimit_of_isSuccArchimedean : ¬ IsSuccLimit a :=
- `Nat.instSuccArchimedean` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Order/SuccPred/Nat.lean`: instance : IsSuccArchimedean ℕ :=

### readable-proof-simplification: [Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean#L194-L195)

Declaration: `CliffordAlgebra.contractRight_contractRight`

The proof manually rewrites the definition of `contractRight` twice before applying the left-contraction result. A `simp only` block can express these same steps by their named identities, without the extra definition-expansion bookkeeping.

Proposed change:

Replace the proof with `by simp only [contractRight_eq, reverse_reverse, contractLeft_contractLeft, map_zero]`.

Benefit: This keeps the mathematical argument visible—convert right contraction to left contraction, use its square-zero theorem, and map zero—while avoiding a manually ordered rewrite sequence.

Source evidence:

- `CliffordAlgebra.contractRight_contractRight` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Contraction.lean`:   rw [contractRight_eq, contractRight_eq, reverse_reverse, contractLeft_contractLeft, map_zero]
- `CliffordAlgebra.reverse_reverse` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/LinearAlgebra/CliffordAlgebra/Conjugation.lean`: @[simp]
theorem reverse_reverse : ∀ a : CliffordAlgebra Q, reverse (reverse a) = a :=

### readable-proof-simplification: [TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean#L167-L174)

Declaration: `continuousOn_schwarzChristoffelBoundary`

This proof obtains a local continuous extension and then identifies it pointwise with the canonical boundary map. The earlier theorem `continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one` already gives continuity of that canonical map on any set where the exponent sum is greater than `-1`, and the preceding sum lemma establishes that condition on this interval.

Proposed change:

Replace the proof with:
```lean
  apply continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one
  intro x hx
  rw [sum_filter_eq_zero_of_mem_Ioo a e ha hx]
  norm_num
```

Benefit: This reuses the theorem whose conclusion is exactly the desired continuity and avoids constructing and identifying a second extension. The short proof makes the mathematical reason explicit: the exponent sum vanishes throughout the prevertex-free interval, so it is greater than `-1`.

Source evidence:

- `continuousOn_schwarzChristoffelBoundary` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`:   obtain ⟨L, hL, hLcont, -⟩ :=
    exists_tendsto_schwarzChristoffelPrimitive_sub_eq a e z₀ ha
- `continuousOn_schwarzChristoffelBoundary_of_exponent_sum_gt_neg_one` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`:     ContinuousOn (schwarzChristoffelBoundary a e z₀) s := by
- `sum_filter_eq_zero_of_mem_Ioo` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Analysis/Complex/Conformal/SchwarzChristoffel/Boundary.lean`:     ∑ i with a i = x, e i = 0 := by

### readable-proof-simplification: [TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean#L92-L98)

Declaration: `IsSl2System.structureConstant_mul_structureConstant_neg_neg`

The two hypotheses prove the same root-sum equality in opposite summand orders by repeating the coercion rewrite and abelian normalization. The second equality follows directly from the first by commutativity.

Proposed change:

Replace the `hγα` proof with `have hγα : (β : H → K) = (γ : H → K) + ((-α : Weight K H L) : H → K) := hβγ.trans (by rw [add_comm])`.

Benefit: This reuses the already-established root relation and makes explicit that the cyclic-symmetry input differs only by the order of its summands. The short `add_comm` step remains easy to interpret, while avoiding a second normalization proof.

Source evidence:

- `IsSl2System.structureConstant_mul_structureConstant_neg_neg` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/Algebra/Lie/Weights/StructureConstant/Opposite.lean`: have hγα : (β : H → K) = (γ : H → K) + ((-α : Weight K H L) : H → K) := by
    rw [Weight.coe_neg, hαβ]
    abel
- `ModEq.modEq_sub_iff_add_modEq'` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/Algebra/Group/ModEq.lean`: modEq_sub_iff_add_modEq'.trans <| by rw [add_comm]

### readable-proof-simplification: [TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean](https://github.com/TauCetiProject/TauCeti/blob/e8b7b600c36c975615413059bc967ec218cfefe0/TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean#L139-L148)

Declaration: `map_span_five_eq_pow_four`

The proof constructs a second cyclotomic-extension instance and rewrites the root order from `5` to `5 ^ (0 + 1)` before applying the general theorem. These expressions reduce to the same value, so the extra setup obscures the direct application of the theorem to the canonical primitive root.

Proposed change:

Replace lines 142–148 with:
```lean
  have h := IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow 5 0 hzeta
```

Benefit: This removes a redundant instance proof and a redundant primitive-root conversion while leaving the mathematical idea clear: apply the general ideal-factorization theorem to the canonical fifth root. In Mathlib, the theorem expects the extension and root order with exponent `k + 1`; at `k = 0`, those forms reduce to the fifth-root forms already available here.

Source evidence:

- `TauCeti.NumberField.FifthCyclotomic.map_span_five_eq_pow_four` in `/home/kim/worktrees/lean-quality-indicators/repos/tauceti/TauCeti/NumberTheory/NumberField/WorkedExamples/FifthCyclotomic/Invariants.lean`:   have hzeta := IsCyclotomicExtension.zeta_spec 5 ℚ K
  have hK : IsCyclotomicExtension {5 ^ (0 + 1)} ℚ K := by
    rw [zero_add, pow_one]
    infer_instance
- `IsCyclotomicExtension.Rat.map_eq_span_zeta_sub_one_pow` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-22c725c48122/Mathlib/NumberTheory/NumberField/Cyclotomic/Ideal.lean`: theorem map_eq_span_zeta_sub_one_pow :
    (map (algebraMap ℤ (𝓞 K)) 𝒑) = span {hζ.toInteger - 1} ^ Module.finrank ℚ K := by

### readable-proof-simplification: [LeanPool/KaltonRoberts/DualCert.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/KaltonRoberts/DualCert.lean#L153-L158)

Declaration: `zero_mem_convexHull_of_best_approx`

This uses broad `simp_all` and a separate `convert` to relate the indicator to its additive-function sum, obscuring the short argument: the chosen additive function sums to the negative of Λ applied to the indicator, which is positive by `hΛ_gen`.

Proposed change:

Replace the proof of `h_additiveFunction_a_pos` with:
```lean
  have h_additiveFunction_a_pos : ∀ S : Finset U, f S = M → additiveFunction a S > 0 := by
    intro S hS
    have hΛ_S := clm_indicator'_eq_additiveFunction Λ S
    simp only [ha_def, additiveFunction, Finset.sum_neg_distrib]
    rw [← hΛ_S]
    exact neg_pos.mpr (hΛ_gen S hS)
```

Benefit: The proof directly exposes the sign reversal that drives the argument and uses the existing indicator-sum identity, rather than relying on broad simplification and a final arithmetic tactic.

Source evidence:

- `zero_mem_convexHull_of_best_approx` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`:     have hΛ_S : Λ (S.indicator') = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by
      convert clm_indicator'_eq_additiveFunction Λ S using 1;
    simp_all +decide [ additiveFunction ];
    linarith [ hΛ_gen S hS ];
- `clm_indicator'_eq_additiveFunction` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/KaltonRoberts/DualCert.lean`: lemma clm_indicator'_eq_additiveFunction (Λ : (U → ℝ) →L[ℝ] ℝ) (S : Finset U) :
    Λ S.indicator' = additiveFunction (fun i => Λ (Function.update 0 i 1)) S := by

### readable-proof-simplification: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L288-L290)

Declaration: `log_cancellation`

This reproves the first-segment logarithmic integral even though the file has already established that formula in `integral_seg1_eq_neg_log`.

Proposed change:

Replace the proof of `h1` with `exact integral_seg1_eq_neg_log (ε / r) hεr_pos hεr_lt1`.

Benefit: Reusing the named segment result removes the integral and logarithm rewrite sequence while making the first-segment contribution explicit and easy to recognize.

Source evidence:

- `integral_seg1_eq_neg_log` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: theorem integral_seg1_eq_neg_log (ε : ℝ) (hε : 0 < ε) (_hε1 : ε < 1) :
    ∫ t in ε..1, (t : ℝ)⁻¹ = -Real.log ε := by

### readable-proof-simplification: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L422-L431)

Declaration: `parabolicRieszKernel_tail_le`

The function equality `hfun` is reflexivity: the additional parentheses in its right-hand function do not change the expression. Establishing it by function extensionality adds an unnecessary intermediate step.

Proposed change:

Replace lines 422–431 with:
```lean
      rw [ENNReal.tsum_mul_right, ENNReal.tsum_mul_right]
      rfl
```

Benefit: This removes a vacuous function-extensionality proof while keeping the argument clear: the two tsum rewrites factor out `T` and `N`, leaving the definition of `parabolicTailKernelConstant`.

Source evidence:

- `ENNReal.tsum_mul_right` in `/tmp/nix-shell.1apE0t/luna-file-audit-runtime-gr27_q3q/repos/deps/mathlib-c55e6e786f49/Mathlib/Topology/Algebra/InfiniteSum/ENNReal.lean`: protected theorem tsum_mul_right : ∑' i, f i * a = (∑' i, f i) * a := by

### readable-proof-simplification: [LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean#L183-L183)

Declaration: `RS.taylorCoeffAt_sub_pow_mul`

This local hypothesis is never referenced in the rest of the proof. Keeping it adds an unnecessary step and may lead readers to look for a role it does not have.

Proposed change:

Delete this line; retain the following `hdiff` proof unchanged.

Benefit: The proof becomes shorter without obscuring its argument: the differentiability fact actually needed for `dslope_sub_mul` is `hdiff`, about the powered product.

Source evidence:

- `RS.taylorCoeffAt_sub_pow_mul` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/JacobianDiffgeo/ResidueCalculus/TaylorCoeff.lean`: have hg' : DifferentiableAt ℂ g z₀ := hg.differentiableAt

### readable-proof-simplification: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L118-L120)

Declaration: `scalarTorusRepresentative_memL2On`

`hcellLe` is never used. The conclusion uses `hbase.mono_measure hcubeLe`, so this intermediate inequality adds proof clutter without contributing to the argument.

Proposed change:

Delete the `hcellLe` declaration (lines 118–120); retain `hcubeLe` and `exact hbase.mono_measure hcubeLe`.

Benefit: The proof still makes clear that the cell and cube measures are compared using their almost-everywhere equivalence, but avoids introducing an inequality that plays no role in establishing the result.

Source evidence:

- `AVenhance.Infra.Torus.unitCell_ae_eq_unitCube` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: theorem unitCell_ae_eq_unitCube :
    unitCell 2 =ᵐ[(volume : Measure (Vec 2))] AVenhance.unitCube := by

### readable-proof-simplification: [LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean#L51-L63)

Declaration: `planeCurveToBivariate_X_zero`

The proof reconstructs the standard image of `X 0` under `finSuccEquiv`, even though Mathlib provides a named theorem for this exact case.

Proposed change:

Remove the `hinner` block and retain the subsequent `rw [planeCurveToBivariate]` and `change`; then use `rw [MvPolynomial.finSuccEquiv_X_zero]` before the final `simp`.

Benefit: This uses a well-named library lemma for the coordinate identification instead of reproving it through the implementation of `finSuccEquiv`. The mathematical point—that coordinate 0 becomes the outer polynomial variable—remains just as easy to see.

Source evidence:

- `planeCurveToBivariate_X_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/MarkoffModP/BGS/CorvajaZannier/PlaneCurveAuxiliaryIndependence.lean`:     rw [MvPolynomial.finSuccEquiv_apply]
    simp
- `MvPolynomial.finSuccEquiv_X_zero` in `/home/kim/worktrees/lean-quality-indicators/repos/deps/mathlib-c55e6e786f49/Mathlib/Algebra/MvPolynomial/Equiv.lean`: theorem finSuccEquiv_X_zero : finSuccEquiv R n (X 0) = Polynomial.X := by simp [finSuccEquiv_apply]

### repeated-proof-machinery: [Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean#L274-L293)

Declaration: `Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow and Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow`

Both declarations repeat the same asymptotic reasoning: multiply the two Big-O bounds, use that the base is eventually at least 1 to combine powers, then use monotonicity in the exponent to compare with the target power. The natural-number proof differs only in converting its eventual bound to a real inequality.

Proposed change:

Introduce a shared lemma for an arbitrary `u : α → ℝ` with `1 ≤ᶠ[l] u`: if `f =O[l] fun x => u x ^ a`, `g =O[l] fun x => u x ^ b`, and `a + b ≤ c`, then `f * g =O[l] fun x => u x ^ c`. Prove it once by multiplying the bounds, combining powers using `Real.rpow_add` on the eventual positivity supplied by `u ≥ 1`, and applying exponent monotonicity. Rewrite the real-parameter theorem using `u := id` and `eventually_ge_atTop 1`; rewrite the natural-parameter theorem using `u := fun n => (n : ℝ)` and `Nat.one_le_cast.mpr` to establish the helper's eventual hypothesis. This generalizes the shared result rather than merely relocating a duplicated branch.

Benefit: Readers can find and reuse the underlying product-of-power-bounds result independently of whether the parameter is real or natural. Maintaining the eventual-base and exponent-comparison argument in one proof also prevents the two public results from drifting.

Source evidence:

- `Asymptotics.IsBigO.mul_atTop_rpow_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`:   refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg
    (zero_le_one.trans ht) (a + b))]
  exact Real.rpow_le_rpow_of_exponent_le ht h
- `Asymptotics.IsBigO.mul_atTop_rpow_natCast_of_isBigO_rpow` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Analysis/SpecialFunctions/Pow/Asymptotics.lean`:   refine (hf.mul hg).trans (Eventually.isBigO ?_)
  filter_upwards [eventually_ge_atTop 1] with t ht
  replace ht : 1 ≤ (t : ℝ) := Nat.one_le_cast.mpr ht
  rw [← Real.rpow_add (zero_lt_one.trans_le ht), Real.norm_of_nonneg (Real.rpow_nonneg

### repeated-proof-machinery: [Mathlib/Topology/VectorBundle/Basic.lean](https://github.com/leanprover-community/mathlib4/blob/e3e75e86143b43849829fdcd44a39a6b0fe35234/Mathlib/Topology/VectorBundle/Basic.lean#L275-L292)

Declaration: `Bundle.Trivialization.coordChangeL`

The forward and inverse continuity fields repeat the same chart-composition argument: restrict to the intersection, use continuity of one trivialization's inverse and the other's map, then take the second component. The inverse field repeats the forward block with e and e' swapped, creating two places to maintain the domain and source-membership reasoning.

Proposed change:

Factor the shared argument into a lemma, for example `continuous_coordChange_apply (e e' : Trivialization F (π F E)) (b : B) (hb : b ∈ e.baseSet ∩ e'.baseSet) : Continuous (fun y : F => (e' ⟨b, e.symm b y⟩).2)`. Prove it by the existing `continuousOn.comp_continuous` argument and taking `.snd`. In `continuous_toFun`, after `rw [dite_eq_left hb]`, use this lemma with `e`, `e'`, and `hb`; in `continuous_invFun`, use it with `e'`, `e`, and `hb.symm`. The outside-intersection `continuous_id` cases remain unchanged. This uses the existing imports and preserves the identity extension outside the intersection.

Benefit: Centralizes the chart-domain and source-membership continuity reasoning so the forward and inverse cases share one proof, reducing maintenance risk if the trivialization continuity argument changes.

Source evidence:

- `Bundle.Trivialization.coordChangeL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: continuous_toFun := by
      by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
      · rw [dite_eq_left hb]
        refine (e'.continuousOn.comp_continuous ?_ ?_).snd
        · exact e.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.1 (mem_univ y)
        · exact fun y => e'.mem_source.mpr hb.2
- `Bundle.Trivialization.coordChangeL` in `/home/kim/worktrees/lean-quality-indicators/repos/mathlib/Mathlib/Topology/VectorBundle/Basic.lean`: continuous_invFun := by
      by_cases hb : b ∈ e.baseSet ∩ e'.baseSet
      · rw [dite_eq_left hb]
        refine (e.continuousOn.comp_continuous ?_ ?_).snd
        · exact e'.continuousOn_symm.comp_continuous (Continuous.prodMk_right b) fun y =>
            mk_mem_prod hb.2 (mem_univ y)
        exact fun y => e.mem_source.mpr hb.1

### repeated-proof-machinery: [LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean#L358-L363)

Declaration: `Pattern across `pv_cutoff_F_integrable_delta_1` and `pv_cutoff_integral_seg1_eq_inv``

These proofs independently establish the same substantive cutoff fact: on the truncated first ray, the cutoff is active because the curve norm exceeds ε, and the integrand is 1/t. Both re-derive the threshold inequality using δ = ε/r and invoke the segment norm and integrand formulas. Keeping the identity in one lemma would avoid drift between the integrability and integral-replacement arguments.

Proposed change:

Introduce a shared private lemma, under `hr : 0 < r`, `hε : 0 < ε`, and `hεr : ε < r`, stating that for the cutoff function F and `δ := ε / r`, every `t ∈ Ioo δ 1` satisfies `F t = (↑(t⁻¹) : ℂ)`. Prove it once using `sectorCurve_norm_seg1` to show the cutoff is active and `pv_integrand_seg1` to identify the value. In `pv_cutoff_F_integrable_delta_1` (lines 358–363) and `pv_cutoff_integral_seg1_eq_inv` (lines 504–513), replace the local `h_eq` proofs with this shared result under their existing hypotheses; each consumer can retain its current integrability or almost-everywhere integral argument.

Benefit: Centralizes the geometric cutoff threshold and integrand calculation, so the two arguments use the same verified identity and are easier to maintain. This uses existing declarations and imports; no additional imports are needed.

Source evidence:

- `pv_cutoff_F_integrable_delta_1` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h_eq : ∀ t ∈ Ioo δ (1 : ℝ), F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    dsimp only [F]; simp only [sub_zero]; rw [ite_eq_left]
    · exact pv_integrand_seg1 r hr α t ⟨lt_trans hδ htδ, ht1⟩
    · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
      calc ε = δ * r := by rw [hδ_def]; field_simp
        _ < t * r := by nlinarith
- `pv_cutoff_integral_seg1_eq_inv` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/LeanModularForms/GeneralizedResidueTheory/Residue/SectorCurve.lean`: have h_on_Ioo : ∀ t ∈ Ioo δ 1, F t = (↑(t⁻¹) : ℂ) := fun t ⟨htδ, ht1⟩ => by
    dsimp only [F]; simp only [sub_zero]; rw [ite_eq_left]
    · rw [sectorCurve_seg1 r α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩,
          deriv_sectorCurve_seg1 r α t ⟨lt_trans hδ htδ, ht1⟩]
      have ht_ne : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (lt_trans hδ htδ))
      have hr_ne : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hr)
      push_cast; field_simp
    · rw [sectorCurve_norm_seg1 r hr α t ⟨le_of_lt (lt_trans hδ htδ), le_of_lt ht1⟩]
      calc ε = δ * r := by rw [hδ_def]; field_simp
        _ < t * r := by nlinarith

### repeated-proof-machinery: [LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean#L138-L160)

Declaration: `positiveShell_pairwise, together with Kernel.lean's negativeShell_pairwise`

Both pairwise-disjoint proofs repeat the same substantive argument: a one-step gap between dyadic exponents gives an ordered-radius inequality, which contradicts the inner and outer shell bounds. The negative-shell proof repeats it in both order cases as well. Keeping these proofs separate risks divergence in the geometric separation argument.

Proposed change:

Add an ordered-shell helper in Kernel.lean, for example `parabolicRieszShell_disjoint_of_index_gap {R : ℝ} (hR : 0 < R) {k l : ℤ} (hkl : k + 1 ≤ l) (z : ParabolicPoint) : Disjoint (parabolicRieszShell R k z) (parabolicRieszShell R l z)`. Its proof converts `hkl` to the real-exponent inequality, applies `Real.rpow_le_rpow_of_exponent_le`, multiplies by `hR.le`, and uses the resulting radius bound against the shell bounds. In Tail.lean, replace the two branches with calls to this helper using `Nat.succ_le_of_lt` and casts; in Kernel.lean's `negativeShell_pairwise`, use the helper with the corresponding `Int.negSucc` index inequality, reversing the disjointness orientation in the opposite order case. These uses retain the existing `hR : 0 < R` and index-order hypotheses, and the helper can use the imports already present in Kernel.lean.

Benefit: One helper centralizes the geometric fact that separates dyadic shells. Both the far-field and near-field proofs then only handle their distinct index arithmetic, making the shared reasoning easier to review and maintain.

Source evidence:

- `positiveShell_pairwise` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Tail.lean`: have hpow : (2 : ℝ) ^ ((n : ℝ) + 1) ≤ (2 : ℝ) ^ (m : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le
- `negativeShell_pairwise` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/CaffarelliKohnNirenberg/Foundation/Parabolic/Morrey/Kernel.lean`: have hpow : (2 : ℝ) ^ ((Int.negSucc m : ℝ) + 1) ≤
        (2 : ℝ) ^ (Int.negSucc n : ℝ) := by
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hexp
    have hrad := mul_le_mul_of_nonneg_right hpow hR.le

### repeated-proof-machinery: [LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean](https://github.com/Vilin97/lean-pool/blob/01db1d7049cf9668bda1e9e106875ee1278b43e6/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean#L188-L263)

Declaration: `weakPathRepresentative_pairing_eq_inner and FrozenDriftProblem.initial_pairing_eq_cell_integral`

These two declarations independently carry out substantial duplicated reasoning: replace a cell integral by a torus integral, use almost-everywhere representatives to identify the integrands, and convert the integral of the product into the torus Hilbert pairing. The second proof repeats the same bridge for the initial datum.

Proposed change:

Add a shared lemma in this file with hypotheses `hF : (fun x : Torus => F x) =ᵐ[volume] AVenhance.Infra.Torus.periodicToTorus f` and `hG : (fun x : Torus => G x) =ᵐ[volume] AVenhance.Infra.Torus.periodicToTorus g`, concluding `∫ x in AVenhance.unitCube, f x * g x = inner ℝ F G` for `F G : ScalarTorusL2` and `f g : Vec 2 → ℝ`. Its proof can use the existing cell-integral transfer, `integral_periodicToTorus_eq_unitCell`, `L2.inner_def`, and `integral_congr_ae`. In the first declaration, supply `F := u t`, `G := ψT`, `f := weakPathRepresentative u t`, `g := ψ`, using `htheta` and `htest`; in the second, supply `F := P.initialTorusL2`, `G := ψT`, `f := P.θ₀`, `g := ψ`, using `hθ` and `hψT`. The helper's hypotheses preserve the actual representative assumptions in both uses.

Benefit: A single proof would maintain the measure-transfer and almost-everywhere pairing argument in one place, while making each theorem focus on establishing its representative hypotheses. This is more than moving a duplicated branch: it factors out the common mathematical bridge used by both results.

Source evidence:

- `weakPathRepresentative_pairing_eq_inner` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: _ = ∫ x : Torus, (u t x) * ψT x := by
- `FrozenDriftProblem.initial_pairing_eq_cell_integral` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Parabolic/FourierGalerkin/LimitRepresentation.lean`: _ = ∫ x : Torus,
          AVenhance.Infra.Torus.periodicToTorus
            (fun y : Vec 2 => P.θ₀ y * ψ y) x := by
- `integral_periodicToTorus_eq_unitCell` in `/home/kim/worktrees/lean-quality-indicators/repos/lean-pool/LeanPool/AnomalousDiffusion/AVenhance/Infra/Torus/Basic.lean`: Integration on the torus agrees with integration of the periodic transfer on the unit cell.
