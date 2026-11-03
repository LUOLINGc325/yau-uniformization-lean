import Yau.Proofs.P03ScaledRadialKernel
import Yau.Proofs.P03ConvolutionJets

open scoped Topology ContDiff Convolution
open MeasureTheory

noncomputable section

namespace Yau.NodeProofs.P03Aux

variable {n : ℕ}

def complexScaledKernel (t : ℝ) (x : ComplexVector n) : ℂ := scaledRadialKernel t x

theorem complexScaledKernel_contDiff (t : ℝ) :
    ContDiff ℝ ∞ (complexScaledKernel (n := n) t) :=
  Complex.ofRealCLM.contDiff.comp (scaledRadialKernel_contDiff t)

theorem complexScaledKernel_tsupport_subset {t : ℝ} (ht : 0 < t) :
    tsupport (complexScaledKernel (n := n) t) ⊆ Metric.closedBall 0 t :=
  (tsupport_comp_subset (g := Complex.ofReal) (by simp) (scaledRadialKernel t)).trans
    (scaledRadialKernel_tsupport_subset ht)

theorem complexScaledKernel_hasCompactSupport {t : ℝ} (ht : 0 < t) :
    HasCompactSupport (complexScaledKernel (n := n) t) :=
  (scaledRadialKernel_hasCompactSupport ht).comp_left (g := Complex.ofReal) (by simp)

theorem scalarConvolution_complexScaledKernel (f : ComplexVector n → ℂ) (t : ℝ) :
    scalarConvolution f (complexScaledKernel t) = smoothBy (scaledRadialKernel t) f := by
  rw [smoothBy_eq_cmulConv]
  funext x
  change (∫ y, f y • complexScaledKernel t (x - y)) =
    ∫ y, f y * (scaledRadialKernel t (x - y) : ℂ)
  simp only [smul_eq_mul, complexScaledKernel]

theorem exists_complexScaledKernel_jet_bound (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (t : ℝ), 0 < t → ∀ x : ComplexVector n,
      ‖iteratedFDeriv ℝ j (complexScaledKernel t) x‖ ≤
        (t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * (t⁻¹) ^ j * C := by
  obtain ⟨C, hC, hb⟩ := exists_scaledRadialKernel_jet_bound (n := n) j
  refine ⟨‖Complex.ofRealCLM‖ * C, mul_nonneg (norm_nonneg _) hC, ?_⟩
  intro t ht x
  have he := Complex.ofRealCLM.iteratedFDeriv_comp_left (x := x)
    (scaledRadialKernel_contDiff (n := n) t).contDiffAt
    (show (j : ℕ∞ω) ≤ ∞ by simp)
  change iteratedFDeriv ℝ j (complexScaledKernel t) x = _ at he
  rw [he]
  calc
    _ ≤ ‖Complex.ofRealCLM‖ * ‖iteratedFDeriv ℝ j (scaledRadialKernel t) x‖ :=
      Complex.ofRealCLM.norm_compContinuousMultilinearMap_le _
    _ ≤ ‖Complex.ofRealCLM‖ *
        ((t ^ Module.finrank ℝ (ComplexVector n))⁻¹ * (t⁻¹) ^ j * C) :=
      mul_le_mul_of_nonneg_left (hb t ht x) (norm_nonneg _)
    _ = _ := by ring

end Yau.NodeProofs.P03Aux
