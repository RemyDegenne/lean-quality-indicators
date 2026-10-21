namespace OAI

namespace PolynomialVacuumAlgebra

namespace AnalyticVacuum

open Classical Filter

open scoped Topology

theorem analytic_normalizedVacuum (N : ℕ) (s : Fin N → Spin) :
    AnalyticAt ℂ (fun X=>normalizedVacuum N X s) (fun _=>1) :=
  (analytic_matrix_adjugate _ (analytic_vacuumResolvent N _) s _).div
    (analytic_matrix_det _ (analytic_vacuumResolvent N _)) (vacuumResolvent_det_ne_zero N)

end AnalyticVacuum
end PolynomialVacuumAlgebra
end OAI
