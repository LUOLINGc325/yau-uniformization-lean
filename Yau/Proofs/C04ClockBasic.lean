import Yau.Proofs.F02Elementary
import Yau.Blueprint.Nodes

/-! The physical-time clock of the original localized flow. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

/-- Restriction of the supplied joint smoothness to its actual time line. -/
theorem timeSlice_contDiffOn {M : ComplexManifold n} {f : M.Carrier → ℝ → ℝ}
    {I : Set ℝ} (hf : SmoothSpaceTime f I) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (f x) I := by
  have hv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hc := (hf x).comp
    (contDiff_const.prodMk contDiff_id).contDiffOn
    (fun t ht => ⟨mem_extChartAt_target x, ht⟩)
  change ContDiffOn ℝ ∞ (fun t => f (chartInv x (chartPt x x)) t) I at hc
  simpa only [hv] using hc

/-- The clock derivative is obtained from the original potential derivative. -/
theorem rho_hasDerivAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (ρ x) (scalarCurvature (h t) x) t := by
  have hP := (hf.2.2.2.2.2.2.2.2.2.2.1 x t ht.le).1.hasDerivAt
    (Ici_mem_nhds ht)
  have heq : ρ x =ᶠ[𝓝 t] fun s => -P x s := by
    filter_upwards [Ici_mem_nhds ht] with s hs
    exact (hf.2.2.2.2.2.2.2.2.2.1 x s hs).1
  simpa only [neg_neg] using hP.neg.congr_of_eventuallyEq heq

/-- Scalar curvature is smooth in positive physical time, using the same rho. -/
theorem scalar_contDiffAt (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (x : Pt X) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ ∞ (fun s => scalarCurvature (h s) x) t := by
  have hc := (timeSlice_contDiffOn hf.2.2.2.1 x).contDiffAt (Ici_mem_nhds ht)
  have heq : (fun s => scalarCurvature (h s) x) =ᶠ[𝓝 t] deriv (ρ x) := by
    filter_upwards [Ioi_mem_nhds ht] with s hs
    exact (rho_hasDerivAt X o h U P ρ hf x hs).deriv.symm
  exact (hc.derivWithin (by simp)).congr_of_eventuallyEq heq

/-- The scalar Harnack inequality at the zero vector is exactly q' >= 0. -/
theorem clockSpeed_deriv_nonneg (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {t : ℝ} (ht : 0 < t) :
    0 ≤ deriv (clockSpeed o h) t := by
  have hd := (scalar_contDiffAt X o h U P ρ hf o ht).differentiableAt (by simp)
  have hq := (hasDerivAt_id t).mul hd.hasDerivAt
  have hLi := hH.2.2.2.2.1 o t ht (0 : ComplexVector n)
  simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero, Complex.zero_re,
    WithLp.ofLp_zero, Matrix.mulVec_zero, dotProduct_zero, add_zero] at hLi
  have hmul := mul_nonneg ht.le hLi
  change 0 ≤ deriv (id * fun s => scalarCurvature (h s) o) t
  rw [hq.deriv]
  simp only [one_mul, id_eq]
  simp only [mul_add, ← mul_assoc, mul_inv_cancel₀ ht.ne', one_mul,
    mul_zero, add_zero] at hmul
  linarith

/-- q is nondecreasing on every positive-time lower ray. -/
theorem clockSpeed_monotoneOn (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {A : ℝ} (hA : 0 < A) :
    MonotoneOn (clockSpeed o h) (Set.Ici A) := by
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Ici A)
  · intro t ht
    exact ((continuousAt_id.mul
      (scalar_contDiffAt X o h U P ρ hf o (hA.trans_le ht)).continuousAt)).continuousWithinAt
  · intro t ht
    have htpos : 0 < t := hA.trans_le (interior_subset ht)
    have hd := (scalar_contDiffAt X o h U P ρ hf o htpos).differentiableAt (by simp)
    exact ((hasDerivAt_id t).mul hd.hasDerivAt).hasDerivWithinAt
  · intro t ht
    have htpos : 0 < t := hA.trans_le (interior_subset ht)
    have hd := (scalar_contDiffAt X o h U P ρ hf o htpos).differentiableAt (by simp)
    have hq := (hasDerivAt_id t).mul hd.hasDerivAt
    have hh := clockSpeed_deriv_nonneg X o h U P ρ hf hH htpos
    change 0 ≤ deriv (id * fun s => scalarCurvature (h s) o) t at hh
    rw [hq.deriv] at hh
    exact hh

/-- The fixed basepoint scalar bound gives the original q <= C t clause. -/
theorem clockSpeed_linear_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (hH : HarnackCompleteness X o h) :
    ∃ C, ∀ t, 1 ≤ t → clockSpeed o h t ≤ C * t := by
  obtain ⟨C, hC⟩ := hH.2.2.2.2.2.2.1
  refine ⟨C, fun t ht => ?_⟩
  exact (mul_le_mul_of_nonneg_left (hC t (zero_le_one.trans ht))
    (zero_le_one.trans ht)).trans_eq (mul_comm t C)

end Yau.Proofs.C04Aux
