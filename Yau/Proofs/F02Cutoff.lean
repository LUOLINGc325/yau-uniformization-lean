import Yau.Proofs.F02Elementary

/-! Compact cutoffs constructed from the registered controlled exhaustion. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.F02Aux
open Yau Blueprint
open LeafProofs.L18Aux

variable {n : ℕ}

def exhaustionCutoffProfile : ContDiffBump (0 : ℝ) :=
  ⟨2, 3, by norm_num, by norm_num⟩

theorem exhaustionCutoffProfile_derivative_bounds :
    ∃ B : ℝ, 0 < B ∧ ∀ s : ℝ,
      |deriv exhaustionCutoffProfile s| ≤ B ∧
        |deriv (deriv exhaustionCutoffProfile) s| ≤ B := by
  have hd : ContDiff ℝ ∞ (deriv exhaustionCutoffProfile) :=
    (contDiff_infty_iff_deriv.mp exhaustionCutoffProfile.contDiff).2
  have hdd : ContDiff ℝ ∞ (deriv (deriv exhaustionCutoffProfile)) :=
    (contDiff_infty_iff_deriv.mp hd).2
  obtain ⟨B₁, hB₁⟩ :=
    (exhaustionCutoffProfile.hasCompactSupport.deriv.norm.isCompact_range hd.continuous.norm).bddAbove
  obtain ⟨B₂, hB₂⟩ :=
    (exhaustionCutoffProfile.hasCompactSupport.deriv.deriv.norm.isCompact_range hdd.continuous.norm).bddAbove
  refine ⟨1 + |B₁| + |B₂|, by positivity, fun s => ?_⟩
  have hb₁ := hB₁ (Set.mem_range_self s)
  have hb₂ := hB₂ (Set.mem_range_self s)
  simp only [Real.norm_eq_abs] at hb₁ hb₂
  constructor <;> nlinarith [le_abs_self B₁, le_abs_self B₂, abs_nonneg B₁, abs_nonneg B₂]

def exhaustionCutoff {M : ComplexManifold n} (u : M.Carrier → ℝ)
    (A L : ℝ) (x : M.Carrier) : ℝ := exhaustionCutoffProfile (u x / (A * L))

theorem exhaustionCutoff_smooth {M : ComplexManifold n} {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (A L : ℝ) : SmoothFn (exhaustionCutoff u A L) := by
  intro x
  exact exhaustionCutoffProfile.contDiff.comp_contDiffOn ((hu x).div_const (A * L))

theorem exhaustionCutoff_range {M : ComplexManifold n} (u : M.Carrier → ℝ)
    (A L : ℝ) (x : M.Carrier) : exhaustionCutoff u A L x ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨exhaustionCutoffProfile.nonneg, exhaustionCutoffProfile.le_one⟩

theorem exhaustionCutoff_tsupport_sublevel {M : ComplexManifold n}
    {u : M.Carrier → ℝ} (hu : SmoothFn u) {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    tsupport (exhaustionCutoff u A L) ⊆ {x | u x ≤ 3 * (A * L)} := by
  apply closure_minimal _ (isClosed_le (continuous_of_smoothFn hu) continuous_const)
  intro x hx
  have hb : u x / (A * L) ∈ Metric.ball (0 : ℝ) 3 := by
    rw [← show exhaustionCutoffProfile.rOut = 3 from rfl,
      ← exhaustionCutoffProfile.support_eq]
    exact hx
  have habs : |u x / (A * L)| < 3 := by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero] using hb
  exact ((div_lt_iff₀ (mul_pos hA hL)).mp ((le_abs_self _).trans_lt habs)).le

theorem exhaustionCutoff_compact (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    HasCompactSupport (exhaustionCutoff u A L) :=
  (hu.2.1 (3 * (A * L))).of_isClosed_subset (isClosed_tsupport _)
    (exhaustionCutoff_tsupport_sublevel hu.1 hA hL)

theorem exhaustionCutoff_one_on_ball (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (C : ℝ) (hC : 0 < C)
    (hupper : ∀ x, u x ≤ C * (1 + distFrom X.metric.form o x))
    {A L : ℝ} (hA : C ≤ A) (hApos : 0 < A) (hL : 1 ≤ L) :
    ∀ x ∈ distBall X.metric.form o L, exhaustionCutoff u A L x = 1 := by
  intro x hx
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  have hr : distFrom X.metric.form o x < L :=
    (LeafProofs.L12Aux.mem_distBall_iff X.metric o x hLpos).mp hx
  have hu0 : 0 ≤ u x := zero_le_one.trans (hu.2.2.1 x)
  apply exhaustionCutoffProfile.one_of_mem_closedBall
  change |u x / (A * L) - 0| ≤ 2
  rw [sub_zero, abs_of_nonneg (div_nonneg hu0 (mul_pos hApos hLpos).le)]
  apply (div_le_iff₀ (mul_pos hApos hLpos)).mpr
  calc
    u x ≤ C * (1 + distFrom X.metric.form o x) := hupper x
    _ ≤ C * (2 * L) := mul_le_mul_of_nonneg_left (by linarith) hC.le
    _ ≤ 2 * (A * L) := by nlinarith [mul_nonneg (sub_nonneg.mpr hA) hLpos.le]

theorem exhaustionCutoff_tsupport_ball (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u)
    (C : ℝ) (hC : 0 < C)
    (hlower : ∀ x, C⁻¹ * (1 + distFrom X.metric.form o x) ≤ u x)
    {A L : ℝ} (hA : 0 < A) (hL : 0 < L) :
    tsupport (exhaustionCutoff u A L) ⊆ distBall X.metric.form o ((3 * C * A + 1) * L) := by
  intro x hx
  have huBound := exhaustionCutoff_tsupport_sublevel hu.1 hA hL hx
  have hlo := mul_le_mul_of_nonneg_left (hlower x) hC.le
  have hcan : C * (C⁻¹ * (1 + distFrom X.metric.form o x)) =
      1 + distFrom X.metric.form o x := by rw [← mul_assoc, mul_inv_cancel₀ hC.ne', one_mul]
  rw [hcan] at hlo
  apply (LeafProofs.L12Aux.mem_distBall_iff X.metric o x (by positivity)).mpr
  change distFrom X.metric.form o x < (3 * C * A + 1) * L
  change u x ≤ 3 * (A * L) at huBound
  nlinarith [mul_le_mul_of_nonneg_left huBound hC.le]

theorem exhaustionCutoffProfile_scaled_deriv (R s : ℝ) :
    deriv (fun z => exhaustionCutoffProfile (z / R)) s =
      deriv exhaustionCutoffProfile (s / R) / R := by
  have hb : ContDiff ℝ ∞ exhaustionCutoffProfile := exhaustionCutoffProfile.contDiff
  have hd := (hb.differentiable (by simp) (s / R)).hasDerivAt.comp s
    ((hasDerivAt_id s).div_const R)
  simpa only [Function.comp_def, id_eq, mul_one_div] using hd.deriv

theorem exhaustionCutoffProfile_scaled_secondDeriv (R s : ℝ) :
    deriv (deriv (fun z => exhaustionCutoffProfile (z / R))) s =
      deriv (deriv exhaustionCutoffProfile) (s / R) / R ^ 2 := by
  have hd : Differentiable ℝ (deriv exhaustionCutoffProfile) :=
    (contDiff_infty_iff_deriv.mp exhaustionCutoffProfile.contDiff).2.differentiable (by simp)
  have heq : deriv (fun z => exhaustionCutoffProfile (z / R)) =
      fun z => deriv exhaustionCutoffProfile (z / R) / R :=
    funext (exhaustionCutoffProfile_scaled_deriv R)
  rw [heq]
  have hD := ((hd (s / R)).hasDerivAt.comp s ((hasDerivAt_id s).div_const R)).div_const R
  simpa only [Function.comp_def, id_eq, mul_one_div, div_div, ← pow_two] using hD.deriv

theorem exhaustionCutoff_laplacian_formula {M : ComplexManifold n}
    (g : HermitianField M) {u : M.Carrier → ℝ} (hu : SmoothFn u) (A L : ℝ) (x : M.Carrier) :
    laplacian g (exhaustionCutoff u A L) x =
      deriv exhaustionCutoffProfile (u x / (A * L)) / (A * L) * laplacian g u x +
        deriv (deriv exhaustionCutoffProfile) (u x / (A * L)) / (A * L) ^ 2 *
          gradNormSq g u x := by
  have hF : ContDiff ℝ ∞ (fun z : ℝ => exhaustionCutoffProfile (z / (A * L))) :=
    exhaustionCutoffProfile.contDiff.comp (contDiff_id.div_const (A * L))
  have h := laplacian_scalar_comp g hu
    (fun z : ℝ => exhaustionCutoffProfile (z / (A * L))) x (hF.contDiffAt.of_le (by simp))
  rw [exhaustionCutoffProfile_scaled_deriv, exhaustionCutoffProfile_scaled_secondDeriv,
    scalarGradientPair_eq_twice_gradNormSq g hu x] at h
  change laplacian g (exhaustionCutoff u A L) x = _ at h
  linarith

/-- Both derivatives of the fixed profile are globally controlled, while
its first derivative vanishes in the interior plateau. These facts and
the registered two-sided Hessian bound give the required L^-2 estimate. -/
theorem exhaustionCutoff_laplacian_bound (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ K : ℝ, 0 < K ∧ ∀ A, 1 ≤ A → ∀ L, 1 ≤ L → ∀ x,
      |laplacian X.metric.form (exhaustionCutoff u A L) x| ≤ K / L ^ 2 := by
  obtain ⟨C, hC, hb⟩ := hu.2.2.2
  obtain ⟨B, hB, hder⟩ := exhaustionCutoffProfile_derivative_bounds
  have hlap : ∀ x, |laplacian X.metric.form u x| ≤ n * C / u x := by
    intro x
    have hg : (gMat X.metric.form x).PosDef :=
      hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)
    have hlo := traceWith_mono _ _ _ hg.posSemidef (hb x).2.2.2.1
    have hhi := traceWith_mono _ _ _ hg.posSemidef (hb x).2.2.2.2
    simp only [← Complex.ofReal_div, ← Complex.ofReal_neg] at hlo
    rw [traceWith_real_smul, traceWith_self _ hg] at hlo hhi
    apply abs_le.mpr
    constructor
    · calc
        -(n * C / u x) = -(C / u x) * n := by ring
        _ ≤ laplacian X.metric.form u x := hlo
    · calc
        laplacian X.metric.form u x ≤ C / u x * n := hhi
        _ = n * C / u x := by ring
  let N : ℝ := B * ((n : ℝ) * C + C ^ 2)
  have hN : 0 ≤ N := by dsimp [N]; positivity
  refine ⟨N + 1, by positivity, fun A hA L hL x => ?_⟩
  have hApos : 0 < A := zero_lt_one.trans_le hA
  have hLpos : 0 < L := zero_lt_one.trans_le hL
  let R := A * L
  have hR : 0 < R := mul_pos hApos hLpos
  have hRL : L ≤ R := by dsimp [R]; nlinarith
  have hg0 : 0 ≤ gradNormSq X.metric.form u x := by
    have h := scalarGradientPair_self_nonneg X.metric.form u x
    rw [scalarGradientPair_eq_twice_gradNormSq _ hu.1] at h
    linarith
  have ht₁ : |deriv exhaustionCutoffProfile (u x / R)| / R *
      |laplacian X.metric.form u x| ≤ B / R * ((n : ℝ) * C / R) := by
    by_cases hx : u x < R
    · have hfrac0 : 0 ≤ u x / R := div_nonneg (zero_le_one.trans (hu.2.2.1 x)) hR.le
      have hfrac1 : u x / R < 1 := (div_lt_one hR).mpr hx
      have hball : u x / R ∈ Metric.ball (0 : ℝ) exhaustionCutoffProfile.rIn := by
        change |u x / R - 0| < 2
        rw [sub_zero, abs_of_nonneg hfrac0]
        linarith
      have hd0 : deriv exhaustionCutoffProfile (u x / R) = 0 := by
        rw [exhaustionCutoffProfile.eventuallyEq_one_of_mem_ball hball |>.deriv_eq]
        simp
      rw [hd0, abs_zero, zero_div, zero_mul]
      positivity
    · exact mul_le_mul
        (div_le_div_of_nonneg_right (hder (u x / R)).1 hR.le)
        ((hlap x).trans (div_le_div_of_nonneg_left (by positivity) hR (le_of_not_gt hx)))
        (abs_nonneg _) (div_nonneg hB.le hR.le)
  have ht₂ : |deriv (deriv exhaustionCutoffProfile) (u x / R)| / R ^ 2 *
      gradNormSq X.metric.form u x ≤ B / R ^ 2 * C ^ 2 :=
    mul_le_mul (div_le_div_of_nonneg_right (hder (u x / R)).2 (sq_nonneg _))
      (hb x).2.2.1 hg0 (div_nonneg hB.le (sq_nonneg _))
  calc
    |laplacian X.metric.form (exhaustionCutoff u A L) x| =
        |deriv exhaustionCutoffProfile (u x / R) / R * laplacian X.metric.form u x +
          deriv (deriv exhaustionCutoffProfile) (u x / R) / R ^ 2 * gradNormSq X.metric.form u x| :=
      congrArg abs (exhaustionCutoff_laplacian_formula _ hu.1 A L x)
    _ ≤ |deriv exhaustionCutoffProfile (u x / R) / R * laplacian X.metric.form u x| +
        |deriv (deriv exhaustionCutoffProfile) (u x / R) / R ^ 2 * gradNormSq X.metric.form u x| :=
      abs_add_le _ _
    _ = |deriv exhaustionCutoffProfile (u x / R)| / R * |laplacian X.metric.form u x| +
        |deriv (deriv exhaustionCutoffProfile) (u x / R)| / R ^ 2 * gradNormSq X.metric.form u x := by
      rw [abs_mul, abs_mul, abs_div, abs_div, abs_of_pos hR,
        abs_of_pos (sq_pos_of_pos hR), abs_of_nonneg hg0]
    _ ≤ B / R * ((n : ℝ) * C / R) + B / R ^ 2 * C ^ 2 := add_le_add ht₁ ht₂
    _ = N / R ^ 2 := by dsimp [N]; ring
    _ ≤ N / L ^ 2 := div_le_div_of_nonneg_left hN (sq_pos_of_pos hLpos)
      ((sq_le_sq₀ hLpos.le hR.le).mpr hRL)
    _ ≤ (N + 1) / L ^ 2 := div_le_div_of_nonneg_right (by linarith) (sq_nonneg _)

end Yau.Proofs.F02Aux
