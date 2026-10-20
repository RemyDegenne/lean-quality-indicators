@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

section

@[expose] public section

noncomputable section

namespace GerverSofa

namespace PartC

namespace Stage2

theorem rhoC_nonneg {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    0 ≤ rhoC t := by
  unfold rhoC
  split_ifs with hφ hθ hη hτ
  · norm_num
  · exact rhoC_phase2_nonneg ht.1
  · exact rhoC_phase3_nonneg ht.1
  · have hηt : eta ≤ t := le_of_lt (lt_of_not_ge hη)
    exact rhoC_phase4_nonneg hηt hτ
  · norm_num

end Stage2
end PartC
end GerverSofa
end
end
end
end
end
end
end
end
