public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

theorem input15208F112_of_cases_F4 (h15206 : StageLemma15206_F4)
    (h33 : Input15208F112At_F4 (Equiv.Perm (Fin 3)) (Equiv.Perm (Fin 3)))
    (h3d : Input15208F112At_F4 (Equiv.Perm (Fin 3)) (DihedralGroup 5))
    (h3s : Input15208F112At_F4 (Equiv.Perm (Fin 3)) ↥(CFSG.Open.Sz 0))
    (h53 : Input15208F112At_F4 (Equiv.Perm (Fin 5)) (Equiv.Perm (Fin 3)))
    (h5d : Input15208F112At_F4 (Equiv.Perm (Fin 5)) (DihedralGroup 5))
    (h5s : Input15208F112At_F4 (Equiv.Perm (Fin 5)) ↥(CFSG.Open.Sz 0)) : Input15208F112_F4 := by
  intro G _ _ T Mc M hs H hH
  obtain ⟨Y₁, hY₁⟩ := h15206 G T Mc M hs
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rcases hY₁.quot with q | q | q
    · exact h33 G T Mc M hs H hH Y₁ hY₁ h q
    · exact h3d G T Mc M hs H hH Y₁ hY₁ h q
    · exact h3s G T Mc M hs H hH Y₁ hY₁ h q
  · rcases hY₁.quot with q | q | q
    · exact h53 G T Mc M hs H hH Y₁ hY₁ h q
    · exact h5d G T Mc M hs H hH Y₁ hY₁ h q
    · exact h5s G T Mc M hs H hH Y₁ hY₁ h q

end CFSG.Quasithin
end
