import Yau.Proofs.C03MovingEnergyTrace
import Yau.Proofs.P02BisectionalContinuity

/-! Actual positive bisectional curvature along the unperturbed path gives
a strictly negative full energy trace. No uniform constant is needed here. -/

noncomputable section
open Filter MeasureTheory Set
open scoped Topology ContDiff

namespace Yau.Proofs.C03Aux
open Yau Yau.LeafProofs L12Aux L23Aux
open Yau.NodeProofs.P02Aux
set_option backward.isDefEq.respectTransparency false

variable {n : ℕ}

theorem movingEnergy_trace_negative (hn : 1 ≤ n)
    (k : HermitianField (ComplexEuclideanManifold n hn)) (hk : MetricSmooth k)
    (γ W : ℝ → ComplexVector n) (hγ : ContDiff ℝ 3 γ) (hW : ContDiff ℝ 3 W)
    (O : Set (ComplexVector n)) (hO : IsOpen O)
    (himage : MapsTo γ (Icc (0 : ℝ) 1) O)
    (hI : ∀ z ∈ O, ∀ v, chartChristoffelBilin k (0 : ComplexVector n) z
      (Complex.I • v) (Complex.I • v) = -chartChristoffelBilin k (0 : ComplexVector n) z v v)
    (hparallel : ∀ t ∈ Icc (0 : ℝ) 1, ∀ a : ℂ, HasDerivAt (fun s => a • W s)
      (-chartChristoffelBilin k (0 : ComplexVector n) (γ t) (deriv γ t) (a • W t)) t)
    (hpositive : ∀ t ∈ Icc (0 : ℝ) 1,
      0 < coordinateBisectional k (0 : ComplexVector n) (γ t) (deriv γ t) (W t)) :
    fderiv ℝ (fderiv ℝ (sourceEnergy hn k (movingJoint γ W 0))) 0 1 1 +
      fderiv ℝ (fderiv ℝ (sourceEnergy hn k (movingJoint γ W 0))) 0 Complex.I Complex.I < 0 := by
  let R : ℝ → ℝ := fun t => coordinateBisectional k (0 : ComplexVector n) (γ t) (deriv γ t) (W t)
  have hT : Continuous (deriv γ) := (show ContDiff ℝ 2 (deriv γ) from hγ.deriv').continuous
  have hR : Continuous R := by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact coordinateBisectional_continuousAt_comp k hk (0 : ComplexVector n) γ (deriv γ) W t
      hγ.continuous.continuousAt hT.continuousAt hW.continuous.continuousAt
      (by rw [euclidean_chartTarget hn]; trivial)
  have hRi : IntegrableOn R (Icc (0 : ℝ) 1) := hR.continuousOn.integrableOn_Icc
  have hRnonneg : 0 ≤ᵐ[volume.restrict (Icc (0 : ℝ) 1)] R := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with t ht
    exact (hpositive t ht).le
  have hsupp : Icc (0 : ℝ) 1 ⊆ Function.support R := fun t ht => (hpositive t ht).ne'
  have hmeasure : 0 < (volume.restrict (Icc (0 : ℝ) 1)) (Function.support R) := by
    calc
      0 < (volume.restrict (Icc (0 : ℝ) 1)) (Icc (0 : ℝ) 1) := by simp
      _ ≤ _ := measure_mono hsupp
  have hpos : 0 < ∫ t in Icc (0 : ℝ) 1, R t :=
    (integral_pos_iff_support_of_nonneg_ae hRnonneg hRi).mpr hmeasure
  let F := sourceEnergy hn k (movingJoint γ W 0)
  have hF : ContDiff ℝ 2 F := by
    apply contDiffOn_univ.mp
    exact sourceEnergy_contDiffOn hn k hk _ univ univ isOpen_univ isOpen_univ (subset_univ _)
      (movingJoint_contDiffOn γ W 0 univ hγ.contDiffOn hW.contDiffOn)
  have hd (a : ℂ) : mapDirection (mapDirection F a) a 0 = fderiv ℝ (fderiv ℝ F) 0 a a := by
    have H := (mapDirection_hasFDerivAt F (p := (0 : ℂ)) hF.contDiffAt a).fderiv
    have HH := congrArg (fun L : ℂ →L[ℝ] ℝ => L a) H
    exact HH
  change fderiv ℝ (fderiv ℝ F) 0 1 1 + fderiv ℝ (fderiv ℝ F) 0 Complex.I Complex.I < 0
  rw [← hd 1, ← hd Complex.I]
  change mapDirection (mapDirection (sourceEnergy hn k (movingJoint γ W 0)) 1) 1 0 +
    mapDirection (mapDirection (sourceEnergy hn k (movingJoint γ W 0)) Complex.I) Complex.I 0 < 0
  rw [movingEnergy_paired_trace hn k hk γ W 0 hγ hW O hO himage hI hparallel]
  have hp (t : ℝ) :
      2 * realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
        (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) (γ t)
          (W t) (deriv γ t) (W t)) +
      2 * realMetricInChart k (0 : ComplexVector n) (γ t) (deriv γ t)
        (connectionCurvature (chartChristoffelBilin k (0 : ComplexVector n)) (γ t)
          (Complex.I • W t) (deriv γ t) (Complex.I • W t)) = (-2) * R t := by
    have H := connectionCurvature_bisectional_sign k hk (0 : ComplexVector n)
      (z := γ t) (by rw [euclidean_chartTarget hn]; trivial) (deriv γ t) (W t)
    dsimp only [R]
    linarith
  calc
    _ = ∫ t in Icc (0 : ℝ) 1, (-2) * R t := integral_congr_ae (Filter.Eventually.of_forall hp)
    _ = (-2) * ∫ t in Icc (0 : ℝ) 1, R t := integral_const_mul _ _
    _ < 0 := mul_neg_of_neg_of_pos (by norm_num) hpos

end Yau.Proofs.C03Aux
