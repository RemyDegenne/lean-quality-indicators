@[expose] public section

namespace SnubCube

/-- tribonacci constant -/
noncomputable def trib : ℝ :=
  (1 + cbrt (19 + 3 * √33) + cbrt (19 - 3 * √33) ) / 3

end SnubCube
end
