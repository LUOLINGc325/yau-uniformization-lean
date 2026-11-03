import Yau.Proofs.C04RelativeDeterminant
import Yau.Proofs.C04SpatialDensity

/-! Determinant decay gives the lower metric bound for the same localized flow. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem density_determinant_lower (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 ≤ t) :
    HermLE ((Real.exp (-ρ x t) : ℂ) • gMat X.metric.form x) (gMat (h t) x) := by
  have hg : (gMat X.metric.form x).PosDef :=
    LeafProofs.L18Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)
  have hh : (gMat (h t) x).PosDef :=
    LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x) (mem_extChartAt_target x)
  have hrpos : 0 < (gMat (h t) x).det.re / (gMat X.metric.form x).det.re :=
    div_pos (Complex.pos_iff.mp hh.det_pos).1 (Complex.pos_iff.mp hg.det_pos).1
  have heq : Real.exp (-ρ x t) = (gMat (h t) x).det.re / (gMat X.metric.form x).det.re := by
    rw [(hf.2.2.2.2.2.2.2.2.2.1 x t ht).1, neg_neg,
      hf.2.2.2.2.2.2.2.2.1 x t ht, Real.exp_log hrpos]
  rw [heq]
  exact relative_determinant_lower _ _ hh hg (hf.2.2.2.2.1 t ht x)

theorem compact_metric_lower (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) :
    ∀ K : Set (Pt X), IsCompact K → ∃ T : ℝ, ∀ t, T ≤ t → ∀ x ∈ K,
      HermLE ((Real.exp (-2 * ρ o t) : ℂ) • gMat X.metric.form x) (gMat (h t) x) := by
  intro K hK
  obtain ⟨Tr, hr⟩ := compact_rho_ratio X o h U P ρ hf hH K hK 1 zero_lt_one
  obtain ⟨Ts, hs⟩ := (tendsto_atTop_atTop.1 (rho_tendsto_atTop X o h U P ρ hf hH)) 1
  refine ⟨max Tr (max Ts 0), ?_⟩
  intro t ht x hx
  have ht0 : 0 ≤ t := (le_max_right Ts 0).trans ((le_max_right Tr _).trans ht)
  have hspos : 0 < ρ o t := zero_lt_one.trans_le
    (hs t ((le_max_left Ts 0).trans ((le_max_right Tr _).trans ht)))
  have hratio := (abs_le.mp (hr t ((le_max_left _ _).trans ht) x hx)).2
  have hrho : ρ x t ≤ 2 * ρ o t :=
    (div_le_iff₀ hspos).mp (show ρ x t / ρ o t ≤ 2 by linarith)
  have hcoef : Real.exp (-2 * ρ o t) ≤ Real.exp (-ρ x t) :=
    Real.exp_le_exp.mpr (by linarith)
  have hg : (gMat X.metric.form x).PosSemidef :=
    (LeafProofs.L18Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  exact hermLE_trans (hermLE_real_smul_mono _ hg hcoef)
    (density_determinant_lower X o h U P ρ hf x ht0)

end Yau.Proofs.C04Aux
