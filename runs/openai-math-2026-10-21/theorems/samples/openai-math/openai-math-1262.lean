namespace OAI

namespace EditApproximation

namespace BinaryFraction

open Finset

theorem gradientWithWork_value {d : ℕ} (G : ℕ) (linear point : Vector BinaryFraction d) (i : Fin d) :
    ((gradientWithWork G linear point).1.get i).value =
      rationalSmoothedGradient G (fun j => (linear.get j).value) (fun j => (point.get j).value) i := by
  have h := congrArg (fun v : Vector UnreducedRational d => (v.get i).value)
    (gradientWithWork_representation G linear point)
  simp only [vector_map_get, representation_value, UnreducedRational.gradient_value] at h
  simpa only [vector_map_get, representation_value] using h

end BinaryFraction
end EditApproximation
end OAI
