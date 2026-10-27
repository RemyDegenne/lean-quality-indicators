public section

namespace CFSG.ClassicalInvolution

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Schreier
  CFSG.Sporadic.Th CFSG.Sporadic.Schreier.Native

theorem noNonsolvableClassical_M22 :
    NoNonsolvableClassical NativeSporadic.M22 := by
  obtain ⟨hcov, hcent⟩ := m22_cover_and_centralizers
  have hQ1 : ValidSchreier m22CentQ1 := (m22_oddcore_cent1).1
  rw [← m22Certificate_originalSubgroup]
  refine noNonsolvableClassical_of_reps _ [m22Rep1] ?_ ?_ ?_
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    exact (m22_rep_data1).1
  · intro u hu ho
    obtain ⟨d, hd, c, hc, hud⟩ := hcov u (by simpa using hu) ho
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
    subst hd
    exact ⟨_, by simp, c, hc, hud⟩
  · intro r hr
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
    subst hr
    have h := hcent (m22Rep1, m22CentQ1.originalSubgroup) (by simp)
    unfold CentralizerGood
    rw [h]
    left
    exact exists_normal_pGroup_of_check _ (enumerationTab m22CentQ1) _
      (mem_enumerationTab_iff m22CentQ1 hQ1) 6 m22_U1_check

end CFSG.ClassicalInvolution
end
