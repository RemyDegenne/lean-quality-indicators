namespace OAI

noncomputable section

namespace BinPackingGap

namespace Coverage

variable {I : Instance} {b n : ℕ}

theorem good_key_subset_edge_anchor_image
    (p : Packing I b) (cls : I.Item → Subclass)
    (label : I.Item → Option (Fin n)) (v : Fin n)
    (keyBaseline : I.Item → ℚ) (a : ℚ) :
    keyPrefixAt (I := I) cls label v keyBaseline a \ badAnchorsAt p cls label v ⊆
      roleItems p cls (edgePrefixAt p cls label v keyBaseline a) .anchor := by
  classical
  intro i hi
  obtain ⟨hi, hnotbad⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨_, hcls, hlabel, hbase⟩ := Finset.mem_filter.mp hi
  have hanchor : i ∈ anchorItemsAt (I := I) cls label v :=
    (mem_anchorItemsAt cls label v i).mpr ⟨by rw [hcls]; rfl, hlabel⟩
  have hused : i ∈ roleItems p cls (goodTuplesAt p cls label v) .anchor := by
    by_contra h
    exact hnotbad ((mem_badAnchorsAt p cls label v i).mpr ⟨hanchor, h⟩)
  obtain ⟨t, ht, hti⟩ := Finset.mem_image.mp hused
  have hpattern : p.tablePattern cls t = .edgeJob := by
    have hsub : patternSubclass (p.tablePattern cls t) .anchor = .y :=
      (p.itemAtRole_subclass cls t .anchor).symm.trans ((congrArg cls hti).trans hcls)
    cases hp : p.tablePattern cls t <;> simp_all [patternSubclass]
  have htgood := (mem_goodTuplesAt p cls label v t).mp ht
  have hG : t ∈ edgeTuplesAt p cls label v :=
    (mem_edgeTuplesAt p cls label v t).mpr ⟨htgood.1, htgood.2, hpattern⟩
  apply Finset.mem_image.mpr
  refine ⟨t, Finset.mem_filter.mpr ⟨hG, ?_⟩, hti⟩
  simpa only [hti] using hbase

end Coverage
end BinPackingGap
end
end OAI
