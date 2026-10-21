namespace OAI

namespace WLIdentification

namespace ComparisonSchemas.SpecialImages

variable {r : ℕ} {P E : Type} {S : ComparisonSchemas r P E} {b : E → Bit}
    (I : S.SpecialImages b)

variable [Fintype P] [Fintype E]

omit [Fintype P] [Fintype E] in
theorem admissible_extend {n : ℕ} (hr : 3 ≤ r) (hn : r + 1 < n)
    {U : Finset (S.layout n).Block} {x : (S.layout n).Coordinate → Bit}
    (hu : U.card < r + 1) (hx : I.Admissible n (by omega) U x) (z : (S.layout n).Block) :
    ∃ y, I.Admissible n (by omega) (insert z U) y ∧
      ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a, y c = x c := by
  classical
  obtain ⟨_, cut, hc, A, hA, q, hq, M, hM⟩ := hx
  have hu' : U.card ≤ r := by omega
  have hnew : (insert z U).card ≤ r + 1 := by
    have := Finset.card_insert_le z U
    omega
  obtain ⟨cut', hc'⟩ := S.exists_cuts n (insert z U) (lt_of_le_of_lt hnew hn)
  obtain ⟨A', hA'⟩ := S.goodAddress_exists n hr hnew hc'
  have hsub : U ⊆ insert z U := Finset.subset_insert _ _
  have hc'U := S.avoids_mono hsub hc'
  have finish (q' : S.RealShift) (hq' : ∀ p, q' p ∈ I.values p A')
      (N : (S.layout n).Potential)
      (hN : ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a,
        (S.layout n).translation (S.starShift n cut' b q') N c =
          (S.layout n).translation (S.starShift n cut b q) M c) :
      ∃ y, I.Admissible n (by omega) (insert z U) y ∧
        ∀ a ∈ U, ∀ c ∈ (S.layout n).coordinates a, y c = x c := by
    refine ⟨(S.layout n).translation (S.starShift n cut' b q') N,
      ⟨hnew, cut', hc', A', hA', q', hq', N, fun _ _ _ _ => rfl⟩, ?_⟩
    intro a ha c hc
    exact (hN a ha c hc).trans (hM a ha c hc).symm
  by_cases hw : (S.layout n).Wrapping (by omega) U
  · obtain ⟨q', hq', hshift⟩ := I.wrapping_shift_extension hr hu' hw hc hc'U
      (hA U (Finset.Subset.refl _) hu' hw) (hA' U hsub hu' hw) q hq
    apply finish q' hq' M
    intro a ha c hc
    exact (S.layout n).translation_eq_of_shifts _ _ M hshift ha hc
  · choose q' hq' using fun p => I.nonempty p A'
    obtain ⟨N, hN⟩ := (S.layout n).adjust_potential hr hw (S.starShift n cut b q)
      (S.starShift n cut' b q') M (fun l hl =>
        (S.starShift_link hc b q hl).trans (S.starShift_link hc'U b q' hl).symm)
    exact finish q' hq' N hN

end ComparisonSchemas.SpecialImages
end WLIdentification
end OAI
