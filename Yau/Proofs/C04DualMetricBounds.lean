import Yau.Proofs.C04MetricDecay
import Yau.Proofs.C04InverseOrder
import Yau.Proofs.C04DualLogRate

/-! Two actual metric bounds imply a uniform lower dual logarithmic secant. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint Matrix

variable {n : ℕ}

theorem dual_log_bounds (H G : Herm n) (hH : H.PosDef) (hG : G.PosDef)
    (s c : ℝ) (hlower : HermLE ((Real.exp (-2 * s) : ℂ) • G) H)
    (hupper : HermLE H ((Real.exp (-c * s) : ℂ) • G))
    (v : Fin n → ℂ) (hv : v ≠ 0) :
    c * s + Real.log (Blueprint.Alignment.Y03Proof.matrixForm G⁻¹ v) ≤
      Real.log (Blueprint.Alignment.Y03Proof.matrixForm H⁻¹ v) ∧
    Real.log (Blueprint.Alignment.Y03Proof.matrixForm H⁻¹ v) ≤
      2 * s + Real.log (Blueprint.Alignment.Y03Proof.matrixForm G⁻¹ v) := by
  have hFG : 0 < Blueprint.Alignment.Y03Proof.matrixForm G⁻¹ v := hG.inv.re_dotProduct_pos hv
  have hFH : 0 < Blueprint.Alignment.Y03Proof.matrixForm H⁻¹ v := hH.inv.re_dotProduct_pos hv
  have hlow := inverse_order_of_real_upper H G hH hG (Real.exp (-c * s))
    (Real.exp_pos _) hupper
  have hhigh := matrix_inverse_order ((Real.exp (-2 * s) : ℂ) • G) H
    (hG.smul (Complex.pos_iff.mpr ⟨Real.exp_pos _, by rw [Complex.ofReal_im]⟩)) hH hlower
  rw [inverse_real_smul _ (Real.exp_pos _) G hG] at hhigh
  have hl := matrixForm_order hlow v
  have hu := matrixForm_order hhigh v
  rw [← Complex.ofReal_inv, matrixForm_real_smul, ← Real.exp_neg] at hl hu
  simp only [neg_mul, neg_neg] at hl hu
  constructor
  · have hh := Real.log_le_log (mul_pos (Real.exp_pos (c * s)) hFG) hl
    simpa only [Real.log_mul (Real.exp_pos _).ne' hFG.ne', Real.log_exp] using hh
  · have hh := Real.log_le_log hFH hu
    simpa only [Real.log_mul (Real.exp_pos _).ne' hFG.ne', Real.log_exp] using hh

theorem dualLog_secant_lower (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hCharts : UniformCharts X h) (hStatic : StaticDistortion X) :
    ∃ c, 0 < c ∧ ∃ T, ∀ t u, T ≤ t → T ≤ u → ∀ v : Fin n → ℂ, v ≠ 0 →
      c * ρ o t - 2 * ρ o u ≤ dualLog h o v t - dualLog h o v u := by
  obtain ⟨c, hc, T, hbound⟩ := compact_metric_decay X o h U P ρ hf hH hCharts hStatic
    {o} (isCompact_singleton)
  refine ⟨c, hc, T, ?_⟩
  intro t u ht hu v hv
  have hg : (gMat X.metric.form o).PosDef :=
    LeafProofs.L18Aux.hMat_posDef X.metric.form o (chartPt o o) (mem_extChartAt_target o)
  have hht : (gMat (h t) o).PosDef :=
    LeafProofs.L18Aux.hMat_posDef (h t) o (chartPt o o) (mem_extChartAt_target o)
  have hhu : (gMat (h u) o).PosDef :=
    LeafProofs.L18Aux.hMat_posDef (h u) o (chartPt o o) (mem_extChartAt_target o)
  have hbt := hbound t ht o (Set.mem_singleton o)
  have hbu := hbound u hu o (Set.mem_singleton o)
  have hlt := (dual_log_bounds _ _ hht hg (ρ o t) c hbt.1 hbt.2 v hv).1
  have hlu := (dual_log_bounds _ _ hhu hg (ρ o u) c hbu.1 hbu.2 v hv).2
  change c * ρ o t - 2 * ρ o u ≤
    Real.log (Blueprint.Alignment.Y03Proof.matrixForm (gMat (h t) o)⁻¹ v) -
      Real.log (Blueprint.Alignment.Y03Proof.matrixForm (gMat (h u) o)⁻¹ v)
  linarith

end Yau.Proofs.C04Aux
