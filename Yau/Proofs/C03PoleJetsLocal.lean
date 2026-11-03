import Yau.Proofs.C03PoleJetsMass
import Yau.Proofs.P03HolomorphicCutoffExtension

/-! A compact continuous model is used only inside the analytic kernel
estimate. Its germ, hence both actual jets, is the original function's. -/

noncomputable section
open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace Yau.Proofs.C03Aux.PoleJets

open Yau Yau.NodeProofs.P03Aux
variable {n : ℕ}

theorem real_jets_zero_of_critical_lintegral
    (hn : 1 ≤ n) (f : ComplexVector n → ℂ) (R : ℝ) (hR : 0 < R)
    (hH : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hfinite : (∫⁻ z in Metric.ball (0 : ComplexVector n) R,
      ENNReal.ofReal (weightedDensity (2 * (n + 1)) f z)) < ∞) :
    ∀ j ≤ 1, iteratedFDeriv ℝ j f 0 = 0 := by
  obtain ⟨F, hFc, hfc, hgerm⟩ := exists_continuous_compact_model
    Metric.isOpen_ball hH.continuousOn (Metric.mem_ball_self hR)
  have hV : Metric.ball (0 : ComplexVector n) R ∩ {z | F z = f z} ∈ 𝓝 0 :=
    inter_mem (Metric.ball_mem_nhds 0 hR) hgerm
  obtain ⟨δ, hδ, hδV⟩ := Metric.mem_nhds_iff.mp hV
  have hHF : DifferentiableOn ℂ F (Metric.ball 0 δ) :=
    (hH.mono (fun _ hz => (hδV hz).1)).congr (fun _ hz => (hδV hz).2)
  have hfiniteF : (∫⁻ z in Metric.ball (0 : ComplexVector n) δ,
      ENNReal.ofReal (weightedDensity (2 * (n + 1)) F z)) < ∞ := by
    calc
      _ = ∫⁻ z in Metric.ball (0 : ComplexVector n) δ,
          ENNReal.ofReal (weightedDensity (2 * (n + 1)) f z) := by
        apply lintegral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_ball] with z hz
        unfold weightedDensity
        rw [(hδV hz).2]
      _ ≤ ∫⁻ z in Metric.ball (0 : ComplexVector n) R,
          ENNReal.ofReal (weightedDensity (2 * (n + 1)) f z) :=
        lintegral_mono_set (fun _ hz => (hδV hz).1)
      _ < ∞ := hfinite
  have hW := integrableOn_weightedDensity (2 * (n + 1)) hFc hfiniteF
  have hzero := real_jets_zero_of_finite_density hn F hFc hfc δ hδ hHF hW
  intro j hj
  exact ((hgerm.iteratedFDeriv ℝ j).self_of_nhds).symm.trans (hzero j hj)

end Yau.Proofs.C03Aux.PoleJets
