import Yau.Proofs.F04FlowCofactor
import Yau.Proofs.F02InitialRicci

/-! Positivity and the signed cofactor estimate follow from the same
localized flow. The initial Ricci sign uses its one-sided metric derivative. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.F04Proof

open Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n}

theorem source_nonneg (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (_ht : 0 ≤ t) :
    0 ≤ source X h x t := by
  apply Proofs.F02Aux.traceWith_nonneg
  · exact (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x)
      (mem_extChartAt_target x)).posSemidef
  · exact Proofs.F02Aux.initialRicci_posSemidef X o h U P ρ hloc x

theorem flow_signed_cofactor_bound (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (x : Pt X) (t : ℝ) (ht : 0 ≤ t)
    (B : Matrix (Fin n) (Fin n) ℂ) (b : ℝ) (hb : 0 ≤ b)
    (hlo : HermLE (((-b : ℝ) : ℂ) • gMat X.metric.form x) B)
    (hhi : HermLE B ((b : ℂ) • gMat X.metric.form x)) :
    |traceWith (gMat (h t) x) B| * density ρ x t ≤ (n : ℝ) * b := by
  have hH := (LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x)
    (mem_extChartAt_target x)).posSemidef
  have hl := Proofs.F02Aux.traceWith_mono (gMat (h t) x) _ _ hH hlo
  have hu := Proofs.F02Aux.traceWith_mono (gMat (h t) x) _ _ hH hhi
  rw [Proofs.F02Aux.traceWith_real_smul] at hl hu
  have habs : |traceWith (gMat (h t) x) B| ≤
      b * traceWith (gMat (h t) x) (gMat X.metric.form x) := by
    apply abs_le.mpr
    exact ⟨by linarith, hu⟩
  calc
    _ ≤ (b * traceWith (gMat (h t) x) (gMat X.metric.form x)) * density ρ x t :=
      mul_le_mul_of_nonneg_right habs (density_pos ρ x t).le
    _ = b * (density ρ x t * traceWith (gMat (h t) x) (gMat X.metric.form x)) := by ring
    _ ≤ b * n := mul_le_mul_of_nonneg_left (flow_cofactor_trace_bound o h U P ρ hloc x t ht) hb
    _ = (n : ℝ) * b := by ring

end Yau.F04Proof
