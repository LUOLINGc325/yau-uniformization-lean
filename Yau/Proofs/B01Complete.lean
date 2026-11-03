import Yau.Proofs.B01Metric
import Yau.Proofs.B01Volume

open scoped Manifold Topology ContDiff ENNReal
open MeasureTheory Set Filter

noncomputable section

namespace Yau.Proofs.B01Aux
open Yau Yau.Blueprint Yau.Blueprint.BundlePresentation

def cuspExhaustionScalar (z : ℂ) : ℝ := Real.log (-Real.log ‖z‖)

theorem cuspExhaustionScalar_contDiffAt {z : ℂ} (hz : z ∈ puncturedUnitDisc) :
    ContDiffAt ℝ ∞ cuspExhaustionScalar z := by
  have hn : ContDiffAt ℝ ∞ (fun w : ℂ => ‖w‖) z := contDiffAt_norm ℝ (norm_pos_iff.mp hz.1)
  exact ((hn.log hz.1.ne').neg.log (neg_ne_zero.mpr (Real.log_neg hz.1 hz.2).ne))

theorem cuspExhaustionScalar_fderiv_bound {z : ℂ} (hz : z ∈ puncturedUnitDisc) (w : ℂ) :
    ‖fderiv ℝ cuspExhaustionScalar z w‖ ≤ ‖w‖ / (‖z‖ * (-Real.log ‖z‖)) := by
  have hn : DifferentiableAt ℝ (fun u : ℂ => ‖u‖) z :=
    (contDiffAt_norm ℝ (norm_pos_iff.mp hz.1) : ContDiffAt ℝ ∞ _ z).differentiableAt (by simp)
  have hl : Real.log ‖z‖ < 0 := Real.log_neg hz.1 hz.2
  have hd : fderiv ℝ cuspExhaustionScalar z =
      (-Real.log ‖z‖)⁻¹ • (-(‖z‖⁻¹ • fderiv ℝ (fun u : ℂ => ‖u‖) z)) :=
    (((hn.hasFDerivAt.log hz.1.ne').neg).log (neg_ne_zero.mpr hl.ne)).fderiv
  rw [hd]
  simp only [smul_apply, neg_apply,
    norm_smul, Real.norm_eq_abs, norm_neg, abs_inv, abs_neg,
    abs_of_pos hz.1, abs_of_neg hl]
  calc
    (-Real.log ‖z‖)⁻¹ * (‖z‖⁻¹ * ‖fderiv ℝ (fun u : ℂ => ‖u‖) z w‖) ≤
        (-Real.log ‖z‖)⁻¹ * (‖z‖⁻¹ * ‖w‖) := by
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr (neg_pos.mpr hl).le)
      apply mul_le_mul_of_nonneg_left _ (inv_nonneg.mpr hz.1.le)
      have hb := (fderiv ℝ (fun u : ℂ => ‖u‖) z).le_opNorm w
      simpa only [norm_fderiv_norm hn, one_mul] using hb
    _ = _ := by field_simp

theorem cuspExhaustionScalar_radius {z : ℂ} (hz : z ∈ puncturedUnitDisc) :
    Real.exp (-Real.exp (cuspExhaustionScalar z)) = ‖z‖ := by
  unfold cuspExhaustionScalar
  rw [Real.exp_log (neg_pos.mpr (Real.log_neg hz.1 hz.2)), neg_neg, Real.exp_log hz.1]

theorem cuspExhaustionScalar_annulus {z : ℂ} (hz : z ∈ puncturedUnitDisc)
    (A B : ℝ) (hA : A ≤ cuspExhaustionScalar z) (hB : cuspExhaustionScalar z ≤ B) :
    Real.exp (-Real.exp B) ≤ ‖z‖ ∧ ‖z‖ ≤ Real.exp (-Real.exp A) := by
  rw [← cuspExhaustionScalar_radius hz]
  exact ⟨Real.exp_le_exp.mpr (neg_le_neg (Real.exp_le_exp.mpr hB)),
    Real.exp_le_exp.mpr (neg_le_neg (Real.exp_le_exp.mpr hA))⟩

variable {M : ComplexManifold 1}

def cuspExhaustion (c : DiscCoordinate M) (x : M.Carrier) : ℝ := cuspExhaustionScalar (c x)

theorem cuspExhaustion_smooth (c : DiscCoordinate M) (hc : IsDiscCoordinate c) :
    SmoothFn (cuspExhaustion c) := by
  intro a z hz
  exact ((cuspExhaustionScalar_contDiffAt (disc_mem c hc (chartInv a z))).comp z
    ((disc_inChart_contDiffAt c hc a hz).restrict_scalars ℝ)).contDiffWithinAt

def discRealDerivative (c : DiscCoordinate M) (x : M.Carrier) :
    TangentSpace 𝓘(ℝ, ComplexVector 1) x →L[ℝ] TangentSpace 𝓘(ℝ, ℂ) (c x) :=
  (tangentSpaceCastModel 𝓘(ℝ, ℂ) (c x)).symm.toContinuousLinearMap ∘L
    (((tangentSpaceCastModel 𝓘(ℂ, ℂ) (c x)).toContinuousLinearMap ∘L
      mfderiv (ComplexModel 1) 𝓘(ℂ, ℂ) c x).restrictScalars ℝ) ∘L
        (LeafProofs.L12Aux.realTangentEquiv x).toContinuousLinearMap

theorem disc_hasMFDerivAt_real (c : DiscCoordinate M) (hc : IsDiscCoordinate c) (x : M.Carrier) :
    HasMFDerivAt 𝓘(ℝ, ComplexVector 1) 𝓘(ℝ, ℂ) c x (discRealDerivative c x) := by
  refine ⟨(disc_continuous c hc).continuousAt, ?_⟩
  have hd := (disc_mdifferentiableAt c hc x).hasMFDerivAt.2.restrictScalars ℝ
  convert! hd using 1

theorem cuspExhaustion_mfderiv_apply (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (x : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector 1) x) :
    (show ℝ from mfderiv 𝓘(ℝ, ComplexVector 1) 𝓘(ℝ, ℝ) (cuspExhaustion c) x v) =
      fderiv ℝ cuspExhaustionScalar (c x)
        (discDerivative c x (LeafProofs.L12Aux.realTangentEquiv x v)) := by
  have hf : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) cuspExhaustionScalar (c x) :=
    ((cuspExhaustionScalar_contDiffAt (disc_mem c hc x)).differentiableAt (by simp)).mdifferentiableAt
  have hd := disc_hasMFDerivAt_real c hc x
  have he := mfderiv_comp_apply x hf hd.mdifferentiableAt v
  rw [mfderiv_eq_fderiv, hd.mfderiv] at he
  exact he

theorem cuspDiscField_speed (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (x : M.Carrier) (v : TangentVector M x) :
    Real.sqrt (2 * hermitianNormSq (cuspDiscField c hc x) v) =
      ‖discDerivative c x v‖ / (‖c x‖ * (-Real.log ‖c x‖)) := by
  have hz := disc_mem c hc x
  have hl := Real.log_neg hz.1 hz.2
  have he : 2 * hermitianNormSq (cuspDiscField c hc x) v =
      (‖discDerivative c x v‖ / (‖c x‖ * (-Real.log ‖c x‖))) ^ 2 := by
    unfold cuspDiscField
    rw [discPullbackMetric_normSq]
    simp only [completeDiscDensity, Complex.normSq_eq_norm_sq]
    field_simp [hz.1.ne', hl.ne]
  rw [he, Real.sqrt_sq (div_nonneg (norm_nonneg _) (mul_pos hz.1 (neg_pos.mpr hl)).le)]

theorem cuspExhaustion_mfderiv_bound (c : DiscCoordinate M) (hc : IsDiscCoordinate c)
    (x : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector 1) x) :
    |(show ℝ from mfderiv 𝓘(ℝ, ComplexVector 1) 𝓘(ℝ, ℝ) (cuspExhaustion c) x v)| ≤
      Real.sqrt (2 * hermitianNormSq (cuspDiscField c hc x) (LeafProofs.L12Aux.realTangentEquiv x v)) := by
  rw [cuspExhaustion_mfderiv_apply c hc, cuspDiscField_speed c hc]
  exact cuspExhaustionScalar_fderiv_bound (disc_mem c hc x) _

end Yau.Proofs.B01Aux
