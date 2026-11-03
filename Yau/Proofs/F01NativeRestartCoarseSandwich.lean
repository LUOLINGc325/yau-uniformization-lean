import Yau.Proofs.F01PastedTerminalMetricOrder
import Yau.Proofs.F01RelativeSandwichWiden

/-! The actual pasted extension has one finite comparison constant
with the original background on the complete longer closed interval. -/
noncomputable section
open Set
open scoped Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem native_restart_paste_coarse_sandwich
    (g K : HermitianField M) (h hR : ℝ → HermitianField M)
    {T ε C D : ℝ} (hT : 0 < T) (hε : 0 < ε) (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hR0 : hR 0 = K)
    (hSmooth : MetricFamilySmooth (nativePastedRestartFlow h hR T) (Icc 0 (T + ε / 2)))
    (hflow : ∀ x s, s ∈ Ico 0 T →
      (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef)
    (hRflow : ∀ x s, s ∈ Icc 0 ε →
      (gMat (hR s) x - ((D⁻¹ : ℝ) : ℂ) • gMat K x).PosSemidef ∧
      ((D : ℂ) • gMat K x - gMat (hR s) x).PosSemidef) :
    1 ≤ C * D ∧ ∀ x t, t ∈ Icc 0 (T + ε / 2) →
      (gMat (nativePastedRestartFlow h hR T t) x - ((((C * D)⁻¹ : ℝ) : ℂ)) • gMat g x).PosSemidef ∧
      (((C * D : ℝ) : ℂ) • gMat g x - gMat (nativePastedRestartFlow h hR T t) x).PosSemidef := by
  have hC0 : 0 < C := zero_lt_one.trans_le hC
  have hD0 : 0 ≤ D := zero_le_one.trans hD
  have hCD : C ≤ C * D := by
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hD hC0.le
  have hK := pasted_terminal_metric_order g K h hR hT hε hR0 hSmooth hflow
  refine ⟨one_le_mul_of_one_le_of_one_le hC hD, ?_⟩
  intro x t ht
  by_cases hh : t < T
  · have hgPos : (gMat g x).PosSemidef :=
      (Yau.LeafProofs.L12Aux.hMat_posDef g x (chartPt x x) (mem_extChartAt_target x)).posSemidef
    have hs := relative_matrix_sandwich_widen (G := gMat g x) (H := gMat (h t) x)
      hgPos hC0 hCD (hflow x t ⟨ht.1, hh⟩)
    simpa only [nativePastedRestartFlow, if_pos hh] using hs
  · have hTt : T ≤ t := le_of_not_gt hh
    have hs : t - T ∈ Icc 0 ε := ⟨sub_nonneg.mpr hTt, by linarith [ht.2]⟩
    have hOrder := relative_matrix_sandwich_compose hD0 (hK x) (hRflow x (t - T) hs)
    simpa only [nativePastedRestartFlow, if_neg hh] using hOrder

end Yau.NodeProofs.F01Aux
