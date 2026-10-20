@[expose] public section

namespace Polynomial

open Real

variable (p : ℂ[X])

theorem logMahlerMeasure_mul_eq_add_logMahlerMeasure {p q : ℂ[X]} (hpq : p * q ≠ 0) :
    (p * q).logMahlerMeasure = p.logMahlerMeasure + q.logMahlerMeasure := by
  simp_all [logMahlerMeasure_eq_log_MahlerMeasure, mahlerMeasure_mul, log_mul]

end Polynomial
end
