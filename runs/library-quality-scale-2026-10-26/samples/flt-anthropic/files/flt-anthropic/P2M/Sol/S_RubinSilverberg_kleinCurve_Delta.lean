import Definitions.Def_EllipticCurve_RubinSilverbergFamily
import P2M.Util
namespace P2MW.S_RubinSilverberg_kleinCurve_Delta

open RubinSilverberg

theorem solution {K : Type*} [Field K] [CharZero K] (u : K) : (kleinCurve u).Δ = -kleinV u ^ 5 := by
  simp only [kleinCurve, WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄,
    WeierstrassCurve.b₆, WeierstrassCurve.b₈, kleinH, kleinT, kleinV]
  field_simp
  ring
