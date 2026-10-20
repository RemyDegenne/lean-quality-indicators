@[expose] public section

namespace Distributed2Coloring.LowerBound

namespace N1000000IntersectionCounting

open scoped BigOperators

open Distributed2Coloring.LowerBound.N1000000OrbitalBasis

open Distributed2Coloring.LowerBound.N1000000MaskAtFacts

open Distributed2Coloring.LowerBound.N1000000OrbitCounting

open Distributed2Coloring.LowerBound.N1000000PairTransitivity

open Distributed2Coloring.LowerBound.N1000000StructureConstants

theorem decode_encodeInter {k : DirIdx} (u : BaseOrbit k) (a d : DirIdx)
    (hcons : consistent (maskAt k) (maskAt a) (maskAt d) = true)
    (w : Inter u a d) :
    decodeInter (u := u) (a := a) (d := d) hcons
      (encodeInter (u := u) (a := a) (d := d) w) = w := by
  classical
  -- Two elements of `Inter` are equal if their underlying vertices are equal.
  apply Subtype.ext
  apply Subtype.ext
  funext j
  -- Split on whether `j` is a free column of `a`.
  by_cases hcol : colMatch (maskAt a) j = none
  · -- free column: evaluate via `decodeTuple_of_colMatch_none` and expand `gOfEmbedding`
    have hv0 :
        (decodeInter (u := u) (a := a) (d := d) hcons
          (encodeInter (u := u) (a := a) (d := d) w)).1.1 j =
          (gOfEmbedding (u := u) (a := a) (d := d) hcons
            (encodeInter (u := u) (a := a) (d := d) w) ⟨j,
            hcol⟩).1 := by
      -- Unfold `decodeInter`/`decodeVertex` and evaluate the decoded tuple at a free column.
      simp [decodeInter, N1000000OrbitCounting.decodeVertex, decodeTuple_of_colMatch_none, hcol]
    -- Now split on `rowMatch d j`.
    cases hrow : rowMatch (maskAt d) j with
    | some l =>
        have hwul : w.1.1 j = u.1.1 l :=
          eq_of_dirMask_rowMatch (u := w.1) (v := u.1) (d := d) (h := w.2.2) (i := j) (j := l) hrow
        -- In this branch, `gOfEmbedding` is forced to `u_l`.
        have hg : (gOfEmbedding (u := u) (a := a) (d := d) hcons
          (encodeInter (u := u) (a := a) (d := d) w) ⟨j,
          hcol⟩).1 =
            u.1.1 l := by
          simpa [gOfEmbedding] using
            (gOfEmbeddingVal_val_of_rowMatch_some (u := u) (a := a) (d := d) (hcons := hcons)
              (e := encodeInter (u := u) (a := a) (d := d) w) (j := (⟨j, hcol⟩ : FreeCol a))
              (l := l) hrow)
        simp [hv0, hg, hwul]
    | none =>
        -- In this branch, `gOfEmbedding` uses the encoded value, which is `w_j`.
        have hg : (gOfEmbedding (u := u) (a := a) (d := d) hcons
          (encodeInter (u := u) (a := a) (d := d) w) ⟨j,
          hcol⟩).1 =
            (encodeInter (u := u) (a := a) (d := d) w ⟨j, ⟨hcol, hrow⟩⟩).1 := by
          simpa [gOfEmbedding] using
            (gOfEmbeddingVal_val_of_rowMatch_none (u := u) (a := a) (d := d) (hcons := hcons)
              (e := encodeInter (u := u) (a := a) (d := d) w) (j := (⟨j, hcol⟩ : FreeCol a)) hrow)
        rw [hv0, hg]
        change
          (encodeInter (u := u) (a := a) (d := d) w
            (⟨j, ⟨hcol, hrow⟩⟩ : FreeCoord a d)).1 = w.1.1 j
        rfl
  · -- fixed column: evaluate via `decodeTuple_of_colMatch_some` and use
    -- `base_eq_of_colMatch` for `w`.
    rcases (Option.ne_none_iff_exists').1 hcol with ⟨i, hi⟩
    have hv0 :
        (decodeInter (u := u) (a := a) (d := d) hcons
          (encodeInter (u := u) (a := a) (d := d) w)).1.1 j =
          baseVertex.1 i := by
      -- Unfold `decodeInter`/`decodeVertex` and evaluate the decoded tuple at a fixed column.
      simp [decodeInter, N1000000OrbitCounting.decodeVertex, decodeTuple_of_colMatch_some, hi]
    -- `w` lies in the base orbit `a`.
    have hw0 : w.1.1 j = baseVertex.1 i :=
      base_eq_of_colMatch (k := a) (u := ⟨w.1, w.2.1⟩) (j := j) (i := i) (h := hi)
    simp [hv0, hw0]

end N1000000IntersectionCounting
end Distributed2Coloring.LowerBound
end
