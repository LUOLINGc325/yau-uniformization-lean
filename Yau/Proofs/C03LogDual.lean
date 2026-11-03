import Yau.Proofs.C03LogDualLog
import Yau.Proofs.C03LogDualOrder

/-! Natural local log-dual estimates for the original computed matrix calculator. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open Set
namespace Yau.Proofs.C03Aux.LogDual
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem smooth_positive_logDual {U : Set (ComplexVector n)}
    (H : ComplexVector n → Herm n)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef) (xi : ComplexVector n) (hxi : xi ≠ 0) :
    ContDiffOn ℝ ∞ (dualSquared H xi) U ∧
      ContDiffOn ℝ ∞ (logDual H xi) U ∧ ∀ z ∈ U, 0 < dualSquared H xi z :=
  ⟨dualSquared_contDiffOn H hH hPos xi, logDual_contDiffOn H hH hPos xi hxi,
    fun z hz => dualSquared_pos (hPos z hz) hxi⟩

theorem logDual_leviC_and_upper {U : Set (ComplexVector n)} (hU : IsOpen U)
    (H : ComplexVector n → Herm n) (hHerm : ∀ z, (H z).IsHermitian)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef)
    (xi : ComplexVector n) (hxi : xi ≠ 0) (kappa d : ℝ) (hd : 0 < d)
    (hLo : ∀ z ∈ U, HermLE ((d : ℂ) • (1 : Herm n)) (H z))
    (hR : ∀ z ∈ U, ∀ a, kappa * dualSquared H xi z * ellipsoidQuadratic (H z) a ≤
      computedResidual H z xi a) :
    ContDiffOn ℝ ∞ (logDual H xi) U ∧ ∀ z ∈ U,
      HermLE ((kappa : ℂ) • H z) (leviC (logDual H xi) z) ∧
        logDual H xi z ≤ max 0 (-Real.log d) + 2 * Real.log (1 + ‖xi‖) :=
  ⟨logDual_contDiffOn H hH hPos xi hxi, fun z hz =>
    ⟨logDual_leviC_lower hU H hHerm hH hPos xi hxi z hz kappa (hR z hz),
      logDual_le_of_lower H z xi hxi (hPos z hz) d hd (hLo z hz)⟩⟩

end Yau.Proofs.C03Aux.LogDual

