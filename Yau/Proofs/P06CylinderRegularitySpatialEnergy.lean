import Yau.Proofs.P06CylinderRegularityLocalEnergy
import Yau.Proofs.P06CylinderRegularityProlongationHeat

/-! Actual square-energy bookkeeping for one step of finite spatial
prolongation. It includes both values and gradients. -/
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1200000
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux.CylinderReg
open Yau.Parabolic Yau.ParabolicCandidates Yau.LeafProofs.L16Aux

variable {n : ℕ} {α : Type*} [Fintype α] [DecidableEq α]

def gradientSquare (U : Point n → α → ℝ) (p : Point n) : ℝ :=
  ∑ r, ∑ i, (spatialGradient (fun q => U q r) p i)^2

theorem prolong_valueSquare (U : Point n → α → ℝ) (p : Point n) :
    valueSquare (regularityProlongValue (fun i => (Yau.realVec i,0)) U) p =
      valueSquare U p + gradientSquare U p := by
  simp only [valueSquare, gradientSquare, Fintype.sum_prod_type, Fintype.sum_option,
    regularityProlongValue, spatialGradient, regularityDirection, Finset.sum_add_distrib]

theorem gradientSquare_nonneg (U : Point n → α → ℝ) (p : Point n) :
    0 ≤ gradientSquare U p :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem weighted_gradient_integrable {Q : Set (Point n)} (hQ : IsOpen Q)
    {η : Point n → ℝ} (hη : Test Q η) {U : Point n → α → ℝ}
    (hU : ∀ r, ContDiffOn ℝ ∞ (fun p => U p r) Q) :
    Integrable (fun p => η p^2 * gradientSquare U p) volume := by
  have hG : ContDiffOn ℝ ∞ (gradientSquare U) Q := by
    apply ContDiffOn.sum
    intro r _
    apply ContDiffOn.sum
    intro i _
    have hD : ContDiffOn ℝ ∞ (fun p => spatialGradient (fun q => U q r) p i) Q := by
      exact ((hU r).fderiv_of_isOpen hQ (m := ∞) (by simp)).clm_apply contDiffOn_const
    exact hD.pow 2
  have hcη2 : HasCompactSupport (fun p => η p^2) := by
    rw [show (fun p => η p^2) = η*η by funext p; rw [Pi.mul_apply,pow_two]]
    exact hη.2.1.mul_right
  have hη2Q : tsupport (fun p => η p^2) ⊆ Q :=
    (tsupport_comp_subset (g := fun s : ℝ => s^2) (by simp) η).trans hη.2.2
  have h := cutoff_contDiff hQ (hη.1.pow 2) hcη2 hη2Q hG
  exact h.1.continuous.integrable_of_hasCompactSupport h.2

theorem inner_gradient_energy_le {Q K : Set (Point n)} (hQ : IsOpen Q)
    (hK : MeasurableSet K) {η : Point n → ℝ} (hη : Test Q η)
    (hηone : ∀ p ∈ K, η p = 1) {U : Point n → α → ℝ}
    (hU : ∀ r, ContDiffOn ℝ ∞ (fun p => U p r) Q) :
    (∫ p in K, gradientSquare U p) ≤ ∫ p, η p^2 * gradientSquare U p := by
  have hInt := weighted_gradient_integrable hQ hη hU
  have hNonneg : ∀ p, 0 ≤ η p^2 * gradientSquare U p :=
    fun p => mul_nonneg (sq_nonneg _) (gradientSquare_nonneg U p)
  have hEq : (∫ p in K, gradientSquare U p) =
      ∫ p in K, η p^2 * gradientSquare U p := by
    apply setIntegral_congr_fun hK
    intro p hp
    simp only [hηone p hp, one_pow, one_mul]
  rw [hEq]
  exact setIntegral_le_integral hInt (Filter.Eventually.of_forall hNonneg)

theorem integral_valueSquare_mono {Q K : Set (Point n)} (hKQ : K ⊆ Q)
    {U : Point n → α → ℝ} (hInt : IntegrableOn (valueSquare U) Q) :
    (∫ p in K, valueSquare U p) ≤ ∫ p in Q, valueSquare U p := by
  exact integral_mono_measure (Measure.restrict_mono hKQ le_rfl)
    (Filter.Eventually.of_forall (fun p => valueSquare_nonneg U p)) hInt

end Yau.NodeProofs.P06Aux.CylinderReg
