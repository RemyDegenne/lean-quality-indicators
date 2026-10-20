@[expose] public section

noncomputable section

namespace AVenhance.Infra.Section4

theorem iterateAmplitudeSq_pos {η : ℝ} (hη : 0 < η) (i : ℕ) :
    0 < iterateAmplitudeSq η i := by
  unfold iterateAmplitudeSq
  split_ifs <;> positivity

end AVenhance.Infra.Section4
end
end
