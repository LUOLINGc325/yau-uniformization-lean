import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Extend
import Mathlib.Analysis.Calculus.FDeriv.RestrictScalars

/-! Polynomially weighted absolute summability of the original coefficients gives actual
smoothness, including all within derivatives, on the closed unit disc. -/

noncomputable section
open Filter
open scoped Topology ContDiff

namespace Yau.Proofs.D06ClosedDiscJets

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]

/-- All polynomial weights are summable for this same coefficient sequence. -/
def AllWeightedSummable (a : ℕ → E) : Prop :=
  ∀ m : ℕ, Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ m * ‖a n‖)

/-- The total power series of the given coefficients. -/
def series (a : ℕ → E) (z : ℂ) : E := ∑' n : ℕ, z ^ n • a n

/-- Actual coefficient differentiation, with the constant coefficient discarded. -/
def derivCoeffs (a : ℕ → E) (n : ℕ) : E := ((n + 1 : ℕ) : ℂ) • a (n + 1)

omit [NormedSpace ℂ E] [CompleteSpace E] in
theorem AllWeightedSummable.norm_summable {a : ℕ → E} (ha : AllWeightedSummable a) :
    Summable (fun n => ‖a n‖) := by
  simpa using ha 0

omit [CompleteSpace E] in
theorem AllWeightedSummable.deriv {a : ℕ → E} (ha : AllWeightedSummable a) :
    AllWeightedSummable (derivCoeffs a) := by
  intro m
  have hs := (summable_nat_add_iff 1).mpr (ha (m + 1))
  apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
  intro n
  simp only [derivCoeffs, norm_smul]
  rw [Complex.norm_natCast]
  simp only [Nat.cast_add, Nat.cast_one]
  have hpow : ((n : ℝ) + 1) ^ m ≤ ((n : ℝ) + 1 + 1) ^ m :=
    pow_le_pow_left₀ (by positivity) (by linarith) m
  calc
    ((n : ℝ) + 1) ^ m * (((n : ℝ) + 1) * ‖a (n + 1)‖) ≤
        ((n : ℝ) + 1 + 1) ^ m * (((n : ℝ) + 1 + 1) * ‖a (n + 1)‖) := by
      exact mul_le_mul hpow (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
        (by positivity) (by positivity)
    _ = (((n : ℝ) + 1 + 1) ^ (m + 1) * ‖a (n + 1)‖) := by
      simp only [pow_succ]; ring

omit [CompleteSpace E] in
theorem norm_term_le {a : ℕ → E} {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1)
    (n : ℕ) : ‖z ^ n • a n‖ ≤ ‖a n‖ := by
  have hz' : ‖z‖ ≤ 1 := by simpa using hz
  rw [norm_smul, norm_pow]
  exact mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ (norm_nonneg _) hz')

theorem summable_series {a : ℕ → E} (ha : AllWeightedSummable a)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    Summable (fun n => z ^ n • a n) :=
  .of_norm_bounded ha.norm_summable (norm_term_le hz)

theorem continuousOn_series {a : ℕ → E} (ha : AllWeightedSummable a) :
    ContinuousOn (series a) (Metric.closedBall (0 : ℂ) 1) := by
  apply continuousOn_tsum (fun n => (by fun_prop : Continuous (fun z : ℂ => z ^ n • a n)).continuousOn)
    ha.norm_summable
  exact fun n z hz => norm_term_le hz n

theorem hasDerivAt_series {a : ℕ → E} (ha : AllWeightedSummable a)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt (series a) (series (derivCoeffs a) z) z := by
  have hu : Summable (fun n : ℕ => (n : ℝ) * ‖a n‖) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ (ha 1)
    intro n
    simp only [pow_one, Nat.cast_add, Nat.cast_one]
    exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _)
  have hb : ∀ (n : ℕ) (w : ℂ), w ∈ Metric.ball (0 : ℂ) 1 →
      ‖((n : ℂ) * w ^ (n - 1)) • a n‖ ≤ (n : ℝ) * ‖a n‖ := by
    intro n w hw
    rw [norm_smul, norm_mul, Complex.norm_natCast, norm_pow]
    have hw' : ‖w‖ ≤ 1 := (by simpa using hw : ‖w‖ < 1).le
    exact mul_le_mul_of_nonneg_right
      (mul_le_of_le_one_right (Nat.cast_nonneg n) (pow_le_one₀ (norm_nonneg _) hw'))
      (norm_nonneg _)
  have hd := hasDerivAt_tsum_of_isPreconnected hu Metric.isOpen_ball
    (convex_ball (0 : ℂ) (1 : ℝ)).isPreconnected
    (fun n w _ => (hasDerivAt_pow n w).smul_const (a n)) hb
    (by simp : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1)
    (summable_series ha (by simp : (0 : ℂ) ∈ Metric.closedBall (0 : ℂ) 1)) hz
  have hs : Summable (fun n : ℕ => ((n : ℂ) * z ^ (n - 1)) • a n) :=
    .of_norm_bounded hu (fun n => hb n z hz)
  have heq : (∑' n : ℕ, ((n : ℂ) * z ^ (n - 1)) • a n) =
      series (derivCoeffs a) z := by
    rw [hs.tsum_eq_zero_add]
    simp only [Nat.cast_zero, zero_mul, zero_smul, zero_add]
    congr 1
    ext n
    simp only [Nat.add_sub_cancel, derivCoeffs, smul_smul]
    congr 1
    ring
  exact heq ▸ hd

section Real

variable [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E]

/-- The real derivative associated to multiplication by a complex vector. -/
def realDerivative : E →L[ℝ] (ℂ →L[ℝ] E) :=
  (ContinuousLinearMap.restrictScalarsIsometry ℂ ℂ E ℝ ℝ).toContinuousLinearMap.comp
    ((ContinuousLinearMap.smulRightL ℂ ℂ E 1).restrictScalars ℝ)

omit [CompleteSpace E] in
@[simp] theorem realDerivative_apply (v : E) (w : ℂ) : realDerivative v w = w • v := rfl

theorem hasFDerivAt_series {a : ℕ → E} (ha : AllWeightedSummable a)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    HasFDerivAt (series a) (realDerivative (series (derivCoeffs a) z)) z :=
  (hasDerivAt_series ha hz).hasFDerivAt.restrictScalars ℝ

theorem closedBall_uniqueDiffOn : UniqueDiffOn ℝ (Metric.closedBall (0 : ℂ) 1) := by
  apply uniqueDiffOn_convex (convex_closedBall _ _)
  rw [interior_closedBall 0 (by norm_num)]
  exact ⟨0, by simp⟩

/-- The actual derivative, including every boundary point of the closed disc. -/
theorem hasFDerivWithinAt_series {a : ℕ → E} (ha : AllWeightedSummable a)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    HasFDerivWithinAt (series a) (realDerivative (series (derivCoeffs a) z))
      (Metric.closedBall (0 : ℂ) 1) z := by
  have hclosure : closure (Metric.ball (0 : ℂ) 1) = Metric.closedBall (0 : ℂ) 1 :=
    closure_ball 0 (by norm_num)
  rw [← hclosure]
  apply hasFDerivWithinAt_closure_of_tendsto_fderiv
    (fun y hy => (hasFDerivAt_series ha hy).differentiableAt.differentiableWithinAt)
    (convex_ball _ _) Metric.isOpen_ball
  · intro y hy
    exact ((continuousOn_series ha) y (hclosure ▸ hy)).mono Metric.ball_subset_closedBall
  · have hlim := (realDerivative.continuous.comp_continuousOn
        (continuousOn_series ha.deriv) z hz).mono Metric.ball_subset_closedBall
    have heq : (fun y => realDerivative (series (derivCoeffs a) y)) =ᶠ[𝓝[Metric.ball (0 : ℂ) 1] z]
        fderiv ℝ (series a) := by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact (hasFDerivAt_series ha hy).fderiv.symm
    exact Filter.Tendsto.congr' heq hlim

/-- Finite smoothness is proved simultaneously for every original coefficient sequence. -/
theorem contDiffOn_series_nat (k : ℕ) {a : ℕ → E} (ha : AllWeightedSummable a) :
    ContDiffOn ℝ k (series a) (Metric.closedBall (0 : ℂ) 1) := by
  induction k generalizing a with
  | zero => exact contDiffOn_zero.mpr (continuousOn_series ha)
  | succ k ih =>
    rw [show ((k + 1 : ℕ) : ℕ∞ω) = (k : ℕ∞ω) + 1 by simp,
      contDiffOn_succ_iff_hasFDerivWithinAt_of_uniqueDiffOn closedBall_uniqueDiffOn]
    refine ⟨by simp, (fun z => realDerivative (series (derivCoeffs a) z)), ?_, ?_⟩
    · exact realDerivative.contDiff.comp_contDiffOn (ih ha.deriv)
    · exact fun z hz => hasFDerivWithinAt_series ha hz

/-- All weighted absolute coefficient sums yield actual closed-disc smoothness of this exact
power series, without selecting an extension or changing any coefficient. -/
theorem contDiffOn_series {a : ℕ → E} (ha : AllWeightedSummable a) :
    ContDiffOn ℝ ∞ (fun z : ℂ => ∑' n : ℕ, z ^ n • a n)
      (Metric.closedBall (0 : ℂ) 1) :=
  contDiffOn_infty.mpr (fun k => contDiffOn_series_nat k ha)

/-- The jets here are the actual iterated within derivatives, rather than supplied fields. -/
theorem continuousOn_iteratedFDerivWithin_series {a : ℕ → E}
    (ha : AllWeightedSummable a) (k : ℕ) :
    ContinuousOn (iteratedFDerivWithin ℝ k (series a) (Metric.closedBall (0 : ℂ) 1))
      (Metric.closedBall (0 : ℂ) 1) :=
  (contDiffOn_series ha).continuousOn_iteratedFDerivWithin (by simp) closedBall_uniqueDiffOn

/-- Recursive differentiated coefficients of the same original sequence. -/
def jetCoeffs (a : ℕ → E) : ℕ → ℕ → E
  | 0 => a
  | k + 1 => derivCoeffs (jetCoeffs a k)

/-- The explicit coefficient series at every derivative order. -/
def jet (a : ℕ → E) (k : ℕ) : ℂ → E := series (jetCoeffs a k)

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] [CompleteSpace E] in
theorem AllWeightedSummable.jetCoeffs {a : ℕ → E} (ha : AllWeightedSummable a) (k : ℕ) :
    AllWeightedSummable (jetCoeffs a k) := by
  induction k with
  | zero => exact ha
  | succ k ih => exact ih.deriv

omit [NormedSpace ℝ E] [IsScalarTower ℝ ℂ E] in
theorem continuousOn_jet {a : ℕ → E} (ha : AllWeightedSummable a) (k : ℕ) :
    ContinuousOn (jet a k) (Metric.closedBall (0 : ℂ) 1) :=
  continuousOn_series (ha.jetCoeffs k)

theorem hasFDerivWithinAt_jet {a : ℕ → E} (ha : AllWeightedSummable a) (k : ℕ)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    HasFDerivWithinAt (jet a k) (realDerivative (jet a (k + 1) z))
      (Metric.closedBall (0 : ℂ) 1) z :=
  hasFDerivWithinAt_series (ha.jetCoeffs k) hz

/-- The same coefficient jet is the actual complex within derivative even on the circle. -/
theorem hasDerivWithinAt_series {a : ℕ → E} (ha : AllWeightedSummable a)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    HasDerivWithinAt (series a) (series (derivCoeffs a) z)
      (Metric.closedBall (0 : ℂ) 1) z := by
  apply HasFDerivWithinAt.of_restrictScalars ℝ (hasFDerivWithinAt_series ha hz)
  rfl

/-- Every explicit jet is the actual iterated derivative of the original power series. -/
theorem iteratedDerivWithin_series {a : ℕ → E} (ha : AllWeightedSummable a) (k : ℕ)
    {z : ℂ} (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    iteratedDerivWithin k (series a) (Metric.closedBall (0 : ℂ) 1) z = jet a k z := by
  induction k generalizing z with
  | zero => rfl
  | succ k ih =>
    rw [iteratedDerivWithin_succ,
      derivWithin_congr (fun y hy => ih hy) (ih hz)]
    exact (hasDerivWithinAt_series (ha.jetCoeffs k) hz).derivWithin
      (closedBall_uniqueDiffOn.mono_field z hz)

/-- The genuine real multilinear jets also have their actual next derivative on the closed disc. -/
theorem hasFDerivWithinAt_iteratedFDerivWithin_series {a : ℕ → E}
    (ha : AllWeightedSummable a) (k : ℕ) {z : ℂ}
    (hz : z ∈ Metric.closedBall (0 : ℂ) 1) :
    HasFDerivWithinAt
      (iteratedFDerivWithin ℝ k (series a) (Metric.closedBall (0 : ℂ) 1))
      (iteratedFDerivWithin ℝ (k + 1) (series a) (Metric.closedBall (0 : ℂ) 1) z).curryLeft
      (Metric.closedBall (0 : ℂ) 1) z :=
  ((contDiffOn_series_nat (k + 1) ha).ftaylorSeriesWithin closedBall_uniqueDiffOn).fderivWithin k
    (by exact_mod_cast Nat.lt_succ_self k) z hz

/-- On the open disc the closed-disc jets agree with the unrestricted actual real derivatives. -/
theorem iteratedFDerivWithin_series_interior {a : ℕ → E}
    (ha : AllWeightedSummable a) (k : ℕ) {z : ℂ}
    (hz : z ∈ Metric.ball (0 : ℂ) 1) :
    iteratedFDerivWithin ℝ k (series a) (Metric.closedBall (0 : ℂ) 1) z =
      iteratedFDeriv ℝ k (series a) z := by
  apply iteratedFDerivWithin_eq_iteratedFDeriv closedBall_uniqueDiffOn
  · exact ((contDiffOn_series_nat k ha).mono Metric.ball_subset_closedBall z hz).contDiffAt
      (Metric.isOpen_ball.mem_nhds hz)
  · exact Metric.ball_subset_closedBall hz

end Real

/-- Scalar form directly matching the entrywise D06 factorization contract. -/
theorem contDiffOn_tsum_mul (a : ℕ → ℂ)
    (ha : ∀ m : ℕ, Summable (fun n => ((n + 1 : ℕ) : ℝ) ^ m * ‖a n‖)) :
    ContDiffOn ℝ ∞ (fun z : ℂ => ∑' n : ℕ, z ^ n * a n)
      (Metric.closedBall (0 : ℂ) 1) := by
  simpa only [smul_eq_mul] using contDiffOn_series ha

end Yau.Proofs.D06ClosedDiscJets
