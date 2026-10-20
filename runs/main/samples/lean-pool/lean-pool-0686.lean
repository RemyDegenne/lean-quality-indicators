@[expose] public section

open MeasureTheory

open Function

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [CompleteSpace E]

theorem PVM.scalarContent_countably_additive_tendsto (E_pvm : PVM E) (x : E)
    (S : ℕ → Set ℝ) (hmeas : ∀ i, MeasurableSet (S i))
    (hpair : Pairwise (Disjoint on S)) :
    Filter.Tendsto (fun n => ∑ i ∈ Finset.range n, E_pvm.scalarContent x (S i))
      Filter.atTop (nhds (E_pvm.scalarContent x (⋃ i, S i))) := by
  have hSOT := E_pvm.countably_additive S hmeas hpair x
  have hinner := Filter.Tendsto.inner (𝕜 := ℂ) hSOT (tendsto_const_nhds :
    Filter.Tendsto (fun _ : ℕ => x) Filter.atTop (nhds x))
  have hre := (Complex.continuous_re.tendsto _).comp hinner
  convert hre using 1
  · funext n
    change (∑ i ∈ Finset.range n,
      (@inner ℂ E _ (E_pvm.proj (S i) x) x).re) =
        (@inner ℂ E _ (∑ i ∈ Finset.range n, E_pvm.proj (S i) x) x).re
    rw [sum_inner, Complex.re_sum]
  · rfl

end
