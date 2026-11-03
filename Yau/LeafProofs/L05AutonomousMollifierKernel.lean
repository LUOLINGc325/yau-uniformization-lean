import Yau.LeafProofs.L05AutonomousAverages
import Mathlib.Analysis.Calculus.BumpFunction.Convolution
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius BoundedContinuousFunction
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoMollifierBump (n : ℕ) (eps : ℝ) (heps : 0< eps) : ContDiffBump (0 : Space n) :=
  ⟨eps/2,eps,half_pos heps,half_lt_self heps⟩

def autoMollifierKernel (n : ℕ) (eps : ℝ) (heps : 0< eps) : Space n → ℝ :=
  (autoMollifierBump n eps heps).normed volume

theorem autoMollifierKernel_nonneg (n : ℕ) (eps : ℝ) (heps : 0< eps) (x : Space n) :
    0≤ autoMollifierKernel n eps heps x := (autoMollifierBump n eps heps).nonneg_normed x

theorem autoMollifierKernel_contDiff (n : ℕ) (eps : ℝ) (heps : 0< eps) :
    ContDiff ℝ ∞ (autoMollifierKernel n eps heps) := (autoMollifierBump n eps heps).contDiff_normed

theorem autoMollifierKernel_integrable (n : ℕ) (eps : ℝ) (heps : 0< eps) :
    Integrable (autoMollifierKernel n eps heps) := (autoMollifierBump n eps heps).integrable_normed

theorem autoMollifierKernel_integral (n : ℕ) (eps : ℝ) (heps : 0< eps) :
    (∫ x, autoMollifierKernel n eps heps x)=1 := (autoMollifierBump n eps heps).integral_normed

theorem autoMollifierKernel_tsupport (n : ℕ) (eps : ℝ) (heps : 0< eps) :
    tsupport (autoMollifierKernel n eps heps)=Metric.closedBall (0 : Space n) eps :=
  (autoMollifierBump n eps heps).tsupport_normed_eq

theorem autoMollifierKernel_compact (n : ℕ) (eps : ℝ) (heps : 0< eps) :
    HasCompactSupport (autoMollifierKernel n eps heps) := (autoMollifierBump n eps heps).hasCompactSupport_normed

theorem autoMollifierKernel_even (n : ℕ) (eps : ℝ) (heps : 0< eps) (x : Space n) :
    autoMollifierKernel n eps heps (-x)=autoMollifierKernel n eps heps x :=
  (autoMollifierBump n eps heps).normed_neg x

/-- The actual nonnegative smooth spatial probability density, not a supplied averaging rule. -/
def autoMollifierMeasure (n : ℕ) (eps : ℝ) (heps : 0< eps) : Measure (Space n) :=
  volume.withDensity (fun x => ENNReal.ofReal (autoMollifierKernel n eps heps x))

theorem autoMollifierMeasure_isProbability (n : ℕ) (eps : ℝ) (heps : 0< eps) :
    IsProbabilityMeasure (autoMollifierMeasure n eps heps) := by
  constructor
  change (volume.withDensity (fun x => ENNReal.ofReal (autoMollifierKernel n eps heps x))) univ=1
  rw [withDensity_apply _ MeasurableSet.univ,setLIntegral_univ,
    ← ofReal_integral_eq_lintegral_ofReal (autoMollifierKernel_integrable n eps heps)
      (ae_of_all volume (autoMollifierKernel_nonneg n eps heps)),autoMollifierKernel_integral,ENNReal.ofReal_one]

theorem autoMollifierMeasure_closedBall_ae (n : ℕ) (eps : ℝ) (heps : 0< eps) :
    ∀ᵐ x ∂autoMollifierMeasure n eps heps, x∈Metric.closedBall (0 : Space n) eps := by
  change ∀ᵐ x ∂volume.withDensity (fun x => ENNReal.ofReal (autoMollifierKernel n eps heps x)), _
  apply (ae_withDensity_iff ((autoMollifierKernel_contDiff n eps heps).continuous.measurable.ennreal_ofReal)).mpr
  exact ae_of_all volume fun x hx => by
    rw [← autoMollifierKernel_tsupport n eps heps]
    apply subset_closure
    intro hz
    exact hx (by rw [hz,ENNReal.ofReal_zero])

theorem autoMollifierMeasure_integral {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [CompleteSpace E] (n : ℕ) (eps : ℝ) (heps : 0< eps) (f : Space n → E) :
    (∫ x, f x ∂autoMollifierMeasure n eps heps)=
      ∫ x, autoMollifierKernel n eps heps x • f x := by
  rw [autoMollifierMeasure,integral_withDensity_eq_integral_toReal_smul
    ((autoMollifierKernel_contDiff n eps heps).continuous.measurable.ennreal_ofReal)
      (ae_of_all volume fun x => ENNReal.ofReal_lt_top) f]
  apply integral_congr_ae
  exact ae_of_all volume fun x => by
    change (ENNReal.ofReal (autoMollifierKernel n eps heps x)).toReal • f x=autoMollifierKernel n eps heps x • f x
    rw [ENNReal.toReal_ofReal (autoMollifierKernel_nonneg n eps heps x)]

end Yau.LeafProofs.L05AutonomousAux
