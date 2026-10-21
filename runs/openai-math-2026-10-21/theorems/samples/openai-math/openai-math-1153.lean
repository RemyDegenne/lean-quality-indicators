namespace OAI

namespace Laughlin.Spin

open scoped Topology

open Filter

theorem threeBodyDimensionRatio_tendsto (z : ℕ) :
    Tendsto (fun Q => threeBodyDimensionRatio Q z) atTop (𝓝 (3/2 : ℝ)) := by
  have h := tendsto_add_mul_div_add_mul_atTop_nhds (-1-2*(z : ℝ)) (-1 : ℝ) 3 (d := 2) (by norm_num)
  convert h using 1
  ext Q
  unfold threeBodyDimensionRatio
  congr 1 <;> ring

end Laughlin.Spin
end OAI
