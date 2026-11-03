import Yau.Proofs.C04RescaledTubeScaling

/-! The original compact metric decay and scalar upper bound control the actual rescaled matrix. -/
noncomputable section
open scoped Topology Manifold ComplexOrder
namespace Yau.Proofs.C05LoopIngressAux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem hermLE_rescale_and_enlarge (A B : Herm n) (hB : B.PosSemidef)
    (r b c : ℝ) (hr : 0 ≤ r) (hbc : r * b ≤ c)
    (hAB : HermLE A ((b : ℂ) • B)) :
    HermLE ((r : ℂ) • A) ((c : ℂ) • B) := by
  have hp := hAB.smul (a := (r : ℂ)) (by exact_mod_cast hr)
  have hq := hB.smul (a := ((c - r * b : ℝ) : ℂ)) (by exact_mod_cast sub_nonneg.mpr hbc)
  have H := hq.add hp
  change (((c : ℂ) • B) - ((r : ℂ) • A)).PosSemidef
  convert H using 1
  ext i j
  simp only [Matrix.add_apply, Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul,
    Complex.ofReal_sub, Complex.ofReal_mul]
  ring

theorem rescaled_metric_order_on_compact (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (hH : HarnackCompleteness X o h)
    (K : Set (Pt X)) (hK : IsCompact K) :
    ∃ B a : ℝ, 0 < B ∧ 0 < a ∧ ∀ t, 1 ≤ t →
      ∀ hR : 0 < scalarCurvature (h t) o, ∀ x ∈ K,
        HermLE (gMat (scaleField (scalarCurvature (h t) o) hR (h t)) x)
          (((B * t ^ (-a) : ℝ) : ℂ) • gMat X.metric.form x) := by
  obtain ⟨C₀, hC₀⟩ := hH.2.2.2.2.2.2.1
  obtain ⟨CK, a, ha, hdec⟩ := hH.2.2.2.2.2.2.2.2 K hK
  let B := max 1 C₀ * max 1 CK
  have h₀ : 0 < max 1 C₀ := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  have hK₀ : 0 < max 1 CK := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  refine ⟨B, a, mul_pos h₀ hK₀, ha, ?_⟩
  intro t ht hR x hx
  have ht₀ : 0 ≤ t := zero_le_one.trans ht
  have hRupper : scalarCurvature (h t) o ≤ max 1 C₀ := (hC₀ t ht₀).trans (le_max_right _ _)
  have hprod : scalarCurvature (h t) o * CK ≤ B :=
    (mul_le_mul_of_nonneg_left (le_max_right 1 CK) hR.le).trans
      (mul_le_mul_of_nonneg_right hRupper hK₀.le)
  have hq : 0 ≤ t ^ (-a) := Real.rpow_nonneg ht₀ _
  have hcoefficient : scalarCurvature (h t) o * (CK * t ^ (-a)) ≤ B * t ^ (-a) := by
    simpa only [mul_assoc] using mul_le_mul_of_nonneg_right hprod hq
  have hG := Yau.LeafProofs.L18Aux.hMat_posDef X.metric.form x (chartPt x x)
    (mem_extChartAt_target x)
  change (gMat X.metric.form x).PosDef at hG
  rw [Yau.Proofs.C04Aux.gMat_scaleField]
  exact hermLE_rescale_and_enlarge _ _ hG.posSemidef _ _ _ hR.le hcoefficient (hdec t ht x hx)

end Yau.Proofs.C05LoopIngressAux
