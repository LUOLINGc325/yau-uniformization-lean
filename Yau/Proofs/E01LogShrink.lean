import Yau.Proofs.E01QuadraticFiber
import Mathlib.Analysis.SpecialFunctions.Log.Basic

/-! A strict radial shrink retains any strict lower bound for log determinant. -/

noncomputable section
open scoped Matrix ComplexOrder Topology
open Filter Set

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {n : ℕ}

theorem continuousAt_logdet_real_smul_one (D : Herm n) (hD : D.PosDef) :
    ContinuousAt (fun r : ℝ => Real.log (((r : ℂ) • D).det.re)) 1 := by
  have hc : Continuous (fun r : ℝ => ((r : ℂ) • D).det.re) := by fun_prop
  apply hc.continuousAt.log
  simpa using ne_of_gt (Complex.pos_iff.mp hD.det_pos).1

theorem exists_positive_shrink_logdet_gt (D : Herm n) (hD : D.PosDef)
    (a : ℝ) (ha : a < Real.log D.det.re) :
    ∃ r : ℝ, 0 < r ∧ r < 1 ∧ a < Real.log (((r : ℂ) • D).det.re) := by
  have hnear : ∀ᶠ r : ℝ in 𝓝 1,
      a < Real.log (((r : ℂ) • D).det.re) :=
    (continuousAt_logdet_real_smul_one D hD).eventually
      (Ioi_mem_nhds (by simpa using ha))
  have hev : ∀ᶠ r : ℝ in 𝓝[<] 1,
      0 < r ∧ r < 1 ∧ a < Real.log (((r : ℂ) • D).det.re) := by
    filter_upwards [hnear.filter_mono nhdsWithin_le_nhds,
      mem_inf_of_left (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)),
      self_mem_nhdsWithin] with r hr hr0 hr1
    exact ⟨hr0, hr1, hr⟩
  exact hev.exists

end Yau.NodeProofs.E01Aux
