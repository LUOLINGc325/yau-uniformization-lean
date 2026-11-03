import Yau.LeafProofs.L22Convex
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.Analysis.Calculus.ContDiff.Convolution
import Mathlib.MeasureTheory.Integral.Pi

noncomputable section

open scoped Topology ContDiff Convolution
open MeasureTheory Set

namespace Yau.LeafProofs.L22Aux

/-- A positive radius even when the requested width is not positive. All
support estimates below assume positivity of the requested width. -/
def regularizedMaxRadius (d : ℝ) : ℝ := if 0 < d then d else 1

theorem regularizedMaxRadius_pos (d : ℝ) : 0 < regularizedMaxRadius d := by
  unfold regularizedMaxRadius
  split_ifs <;> positivity

def regularizedMaxBump (d : ℝ) : ContDiffBump (0 : ℝ) :=
  ⟨regularizedMaxRadius d / 2, regularizedMaxRadius d,
    half_pos (regularizedMaxRadius_pos d), by linarith [regularizedMaxRadius_pos d]⟩

/-- The actual one-dimensional nonnegative even smooth probability kernel. -/
def regularizedMaxKernel (d : ℝ) : ℝ → ℝ := (regularizedMaxBump d).normed volume

theorem regularizedMaxKernel_nonneg (d x : ℝ) : 0 ≤ regularizedMaxKernel d x :=
  (regularizedMaxBump d).nonneg_normed x

theorem regularizedMaxKernel_smooth (d : ℝ) : ContDiff ℝ ∞ (regularizedMaxKernel d) :=
  (regularizedMaxBump d).contDiff_normed

theorem regularizedMaxKernel_compact (d : ℝ) : HasCompactSupport (regularizedMaxKernel d) :=
  (regularizedMaxBump d).hasCompactSupport_normed

theorem regularizedMaxKernel_integrable (d : ℝ) : Integrable (regularizedMaxKernel d) :=
  (regularizedMaxBump d).integrable_normed

theorem regularizedMaxKernel_mass (d : ℝ) : (∫ x, regularizedMaxKernel d x) = 1 :=
  (regularizedMaxBump d).integral_normed

theorem regularizedMaxKernel_even (d x : ℝ) :
    regularizedMaxKernel d (-x) = regularizedMaxKernel d x :=
  (regularizedMaxBump d).normed_neg x

theorem regularizedMaxKernel_support {d x : ℝ}
    (hx : regularizedMaxKernel d x ≠ 0) : |x| < regularizedMaxRadius d := by
  have hmem : x ∈ Function.support ((regularizedMaxBump d).normed volume) := hx
  rw [(regularizedMaxBump d).support_normed_eq] at hmem
  simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, regularizedMaxBump] using hmem

theorem regularizedMaxKernel_support_of_pos {d x : ℝ} (hd : 0 < d)
    (hx : regularizedMaxKernel d x ≠ 0) : |x| < d := by
  simpa only [regularizedMaxRadius, if_pos hd] using regularizedMaxKernel_support hx

theorem regularizedMaxKernel_firstMoment (d : ℝ) :
    (∫ x, x * regularizedMaxKernel d x) = 0 := by
  have heq := integral_neg_eq_self (fun x : ℝ => x * regularizedMaxKernel d x) volume
  simp only [regularizedMaxKernel_even, neg_mul, integral_neg] at heq
  linarith

/-- The product kernel, with one independent coordinate for each active
branch. In particular its marginals are independent of the ambient family. -/
def regularizedMaxProductKernel {κ : Type*} [Fintype κ] (δ : κ → ℝ)
    (x : κ → ℝ) : ℝ := ∏ i, regularizedMaxKernel (δ i) (x i)

theorem regularizedMaxProductKernel_nonneg {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) (x : κ → ℝ) : 0 ≤ regularizedMaxProductKernel δ x :=
  Finset.prod_nonneg (fun i _ => regularizedMaxKernel_nonneg _ _)

theorem regularizedMaxProductKernel_smooth {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) : ContDiff ℝ ∞ (regularizedMaxProductKernel δ) := by
  classical
  apply contDiff_prod
  intro i _
  exact (regularizedMaxKernel_smooth (δ i)).comp (contDiff_apply ℝ (fun _ : κ => ℝ) i)

theorem regularizedMaxProductKernel_compact {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) : HasCompactSupport (regularizedMaxProductKernel δ) := by
  classical
  apply HasCompactSupport.intro
    (isCompact_univ_pi (fun i => isCompact_Icc : ∀ i : κ,
      IsCompact (Icc (-regularizedMaxRadius (δ i)) (regularizedMaxRadius (δ i)))))
  intro x hx
  simp only [mem_univ_pi, mem_Icc, not_forall] at hx
  obtain ⟨i, hi⟩ := hx
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  by_contra hn
  have h := (abs_lt.mp (regularizedMaxKernel_support hn))
  exact hi ⟨h.1.le, h.2.le⟩

theorem regularizedMaxProductKernel_integrable {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) : Integrable (regularizedMaxProductKernel δ) :=
  (regularizedMaxProductKernel_smooth δ).continuous.integrable_of_hasCompactSupport
    (regularizedMaxProductKernel_compact δ)

theorem regularizedMaxProductKernel_mass {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) : (∫ x, regularizedMaxProductKernel δ x) = 1 := by
  simp only [regularizedMaxProductKernel, integral_fintype_prod_volume_eq_prod,
    regularizedMaxKernel_mass, Finset.prod_const_one]

theorem regularizedMaxProductKernel_even {κ : Type*} [Fintype κ]
    (δ : κ → ℝ) (x : κ → ℝ) :
    regularizedMaxProductKernel δ (-x) = regularizedMaxProductKernel δ x := by
  simp only [regularizedMaxProductKernel, Pi.neg_apply, regularizedMaxKernel_even]

end Yau.LeafProofs.L22Aux
