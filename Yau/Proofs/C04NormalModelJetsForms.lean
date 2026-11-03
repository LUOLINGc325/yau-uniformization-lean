import Yau.Proofs.C04NormalModelJetsInverse
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-! Actual model Gram forms and conjugated operators, as continuous maps. -/

noncomputable section
open scoped Topology ContDiff InnerProductSpace

namespace Yau.Proofs.C04Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def normalModelGramBilinear :
    (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) →L[ℝ] E →L[ℝ] E →L[ℝ] ℝ :=
  (2 : ℝ) • ContinuousLinearMap.precompL E
    (ContinuousLinearMap.precompR E (innerSL ℝ (E := E)))

def normalModelMetric (L : E →L[ℝ] E) : E →L[ℝ] E →L[ℝ] ℝ :=
  normalModelGramBilinear L L

def normalModelComplex (I L : E →L[ℝ] E) : E →L[ℝ] E :=
  L.inverse.comp (I.comp L)

@[simp] theorem normalModelMetric_apply (L : E →L[ℝ] E) (u w : E) :
    normalModelMetric L u w = 2 * ⟪L u, L w⟫_ℝ := rfl

@[simp] theorem normalModelComplex_apply (I L : E →L[ℝ] E) (u : E) :
    normalModelComplex I L u = L.inverse (I (L u)) := rfl

theorem normalModelGramBilinear_norm : ‖normalModelGramBilinear (E := E)‖ ≤ 2 := by
  have hh : ‖ContinuousLinearMap.precompL E
      (ContinuousLinearMap.precompR E (innerSL ℝ (E := E)))‖ ≤ 1 :=
    (ContinuousLinearMap.norm_precompL_le E _).trans
      ((ContinuousLinearMap.norm_precompR_le E _).trans (norm_innerSL_le ℝ (E := E)))
  calc
    ‖normalModelGramBilinear (E := E)‖ = 2 * ‖ContinuousLinearMap.precompL E
        (ContinuousLinearMap.precompR E (innerSL ℝ (E := E)))‖ := by
      simp only [normalModelGramBilinear, norm_smul, Real.norm_ofNat]
    _ ≤ 2 * 1 := mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = 2 := by ring

theorem normal_model_metric_contDiff (A : E → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) :
    ContDiff ℝ ∞ (fun x => normalModelMetric (A x)) := by
  exact ((normalModelGramBilinear (E := E)).contDiff.comp hA).clm_apply hA

theorem normal_model_metric_jet_bound (A : E → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A)
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (x : E)
    (hjet : ∀ j, ‖iteratedFDeriv ℝ j A x‖ ≤ B j) (m : ℕ) :
    ‖iteratedFDeriv ℝ m (fun y => normalModelMetric (A y)) x‖ ≤
      2 * ∑ i ∈ Finset.range (m + 1),
        (m.choose i : ℝ) * B i * B (m - i) := by
  have hb := (normalModelGramBilinear (E := E)).norm_iteratedFDeriv_le_of_bilinear
    hA hA x (by simp : (m : ℕ∞ω) ≤ ∞)
  change ‖iteratedFDeriv ℝ m (fun y => normalModelMetric (A y)) x‖ ≤ _ at hb
  apply hb.trans
  gcongr with i hi
  · exact normalModelGramBilinear_norm
  · exact mul_nonneg (Nat.cast_nonneg _) (hB i)
  · exact hjet i
  · exact hjet (m - i)

theorem normal_model_left_composition_jet_bound (I : E →L[ℝ] E) (hI : ‖I‖ ≤ 1)
    (A : E → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (m : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ m (fun y => I.comp (A y)) x‖ ≤ ‖iteratedFDeriv ℝ m A x‖ := by
  let L : (E →L[ℝ] E) →L[ℝ] (E →L[ℝ] E) := ContinuousLinearMap.compL ℝ E E E I
  have hL : ‖L‖ ≤ 1 := by
    calc
      ‖L‖ ≤ ‖ContinuousLinearMap.compL ℝ E E E‖ * ‖I‖ :=
        (ContinuousLinearMap.compL ℝ E E E).le_opNorm I
      _ ≤ 1 * 1 := by gcongr; exact ContinuousLinearMap.norm_compL_le ℝ E E E
      _ = 1 := by ring
  have hh := L.norm_iteratedFDeriv_comp_left (hA.contDiffAt (x := x))
    (by simp : (m : ℕ∞ω) ≤ ∞)
  exact hh.trans (mul_le_of_le_one_left (norm_nonneg _) hL)

variable [CompleteSpace E] [FiniteDimensional ℝ E]

theorem normal_model_complex_contDiffOn (I : E →L[ℝ] E)
    (A : E → E →L[ℝ] E) (hA : ContDiff ℝ ∞ A) (R : ℝ)
    (hnear : ∀ x ∈ Metric.ball (0 : E) R,
      ‖A x - ContinuousLinearMap.id ℝ E‖ ≤ (1 / 4 : ℝ)) :
    ContDiffOn ℝ ∞ (fun x => normalModelComplex I (A x)) (Metric.ball (0 : E) R) :=
  (normal_model_inverse_contDiffOn A hA R hnear).clm_comp
    (contDiffOn_const.clm_comp hA.contDiffOn)

end Yau.Proofs.C04Aux
