import Yau.Proofs.F05BootstrapNormalSmooth
import Yau.Proofs.F05BootstrapInteriorSmooth

/-! Joint positive-time smoothness on genuine closed receiving caps for
both interior and physical charts, including dimensions zero and one. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport
variable {n : ℕ}

theorem F05_zero_trace_cap_smooth {ν : Option (RIdx n)} {T α lam upper r s : ℝ}
    (hT : 0 < T) (hα : 0 < α) (hα1 : α < 1)
    (hr : 0 < r) (hr2 : r < 2) (hs : 0 < s) (hsT : s < T)
    (A : Point n → Mat n) (B : Point n → RIdx n → ℝ) (H J u : Point n → ℝ)
    (hA : ContDiffOn ℝ ∞ A (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hB : ∀ i, ContDiffOn ℝ ∞ (fun z => B z i) (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hH : ContDiffOn ℝ ∞ H (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hJ : ContDiffOn ℝ ∞ J (Metric.ball 0 3 ×ˢ Ioc 0 T))
    (hu : F05LocalSchauder α ν T u) (hFace : F05ZeroFace ν T u)
    (hEll : Elliptic (F05PosPatch ν T) (fun z => Real.exp (-u z) • A z) lam upper)
    (hPDE : ∀ z ∈ F05PosPatch ν T,
      F05RelOp (F05PosSpace ν) (Ioc 0 T) (fun z => Real.exp (-u z) • A z)
        (fun z i => Real.exp (-u z)*B z i) u z = Real.exp (-u z)*H z+J z) :
    ContDiffOn ℝ ∞ u (region ν r ×ˢ Icc s T) := by
  cases ν with
  | none =>
    have hAll := F05_zero_trace_nonlinear_good_words hT hα hα1 A B H J u hA hB hH hJ hu hFace hEll hPDE
    exact F05_interior_good_family_smooth hr hr2 hs hsT u (fun β hβ => (hAll β hβ).1) []
      (by simp [F05GoodList])
  | some j =>
    exact (F05_zero_trace_physical_good_family_smooth j hT hα hα1 hr hr2 hs hsT A B H J u
      hA hB hH hJ hu hFace hEll hPDE).1 [] (by simp [F05GoodList])

end Yau.Proofs.F05Aux
