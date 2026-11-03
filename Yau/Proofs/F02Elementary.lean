import Yau.Blueprint.Analytic
import Yau.LeafProofs.L18

/-! Native matrix and potential identities for the original F02 estimate. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder MatrixOrder
open MeasureTheory Filter

namespace Yau.Proofs.F02Aux
open Yau Blueprint

variable {n : ℕ}

/-- The real trace of a product of two positive semidefinite matrices is
nonnegative, without a commutativity hypothesis. -/
theorem trace_mul_re_nonneg (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : A.PosSemidef) (hB : B.PosSemidef) :
    0 ≤ (Matrix.trace (A * B)).re := by
  let S := CFC.sqrt A
  have hS : S.IsHermitian :=
    (Matrix.nonneg_iff_posSemidef.mp (CFC.sqrt_nonneg A)).isHermitian
  have hSS : S * S = A := CFC.sqrt_mul_sqrt_self A hA.nonneg
  have hp : (S * B * S).PosSemidef := by
    simpa only [hS.eq] using hB.conjTranspose_mul_mul_same S
  have heq : Matrix.trace (S * B * S) = Matrix.trace (A * B) := by
    rw [Matrix.trace_mul_cycle, hSS]
  exact (Complex.nonneg_iff.mp (heq ▸ hp.trace_nonneg)).1

theorem traceWith_nonneg (H A : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) (hA : A.PosSemidef) : 0 ≤ traceWith H A :=
  trace_mul_re_nonneg H⁻¹ A hH.inv hA

theorem traceWith_sub (H A B : Matrix (Fin n) (Fin n) ℂ) :
    traceWith H (A - B) = traceWith H A - traceWith H B := by
  simp only [traceWith, Matrix.mul_sub, Matrix.trace_sub, Complex.sub_re]

theorem traceWith_real_smul (H A : Matrix (Fin n) (Fin n) ℂ) (c : ℝ) :
    traceWith H ((c : ℂ) • A) = c * traceWith H A := by
  simp only [traceWith, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

theorem traceWith_mono (H A B : Matrix (Fin n) (Fin n) ℂ)
    (hH : H.PosSemidef) (hAB : HermLE A B) : traceWith H A ≤ traceWith H B := by
  have hp := traceWith_nonneg H (B - A) hH hAB
  rw [traceWith_sub] at hp
  linarith

theorem traceWith_self (H : Matrix (Fin n) (Fin n) ℂ) (hH : H.PosDef) :
    traceWith H H = n := by
  rw [traceWith, Matrix.nonsing_inv_mul _ (hH.isUnit.map Matrix.detMonoidHom)]
  simp

/-- Both pointwise bounds in F02 follow from the actual metric positivity
and the Loewner inequality supplied by the same localized flow. -/
theorem metricDefect_trace_bounds (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt X) :
    0 ≤ traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x) ∧
      traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x) ≤ n := by
  have hg := LeafProofs.L18Aux.hMat_posDef X.metric.form x (chartPt x x)
    (mem_extChartAt_target x)
  have hh := LeafProofs.L18Aux.hMat_posDef (h t) x (chartPt x x)
    (mem_extChartAt_target x)
  change (gMat X.metric.form x).PosDef at hg
  change (gMat (h t) x).PosDef at hh
  refine ⟨traceWith_nonneg _ _ hg.posSemidef (hf.2.2.2.2.1 t ht x), ?_⟩
  rw [traceWith_sub, traceWith_self _ hg]
  exact sub_le_self _ (traceWith_nonneg _ _ hg.posSemidef hh.posSemidef)

/-- The initial-time metric defect is identically zero. -/
theorem metricDefect_zero (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) (x : Pt X) :
    traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h 0) x) = 0 := by
  rw [hf.1.1, sub_self]
  simp [traceWith]

/-- Taking the actual initial-metric trace of the localized potential
identity gives the scalar identity used in the paper's cutoff argument. -/
theorem metricDefect_potential_identity (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt X) :
    traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x) =
      t * scalarCurvature X.metric.form x - laplacian X.metric.form (fun y => U y t) x := by
  rw [hf.2.2.2.2.2.1 t ht x]
  have hm : gMat X.metric.form x -
      (gMat X.metric.form x - (t : ℂ) • ricci X.metric.form x + levi (fun y => U y t) x) =
      (t : ℂ) • ricci X.metric.form x - levi (fun y => U y t) x := by abel
  rw [hm, traceWith_sub]
  simp only [traceWith, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul,
    Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    scalarCurvature, laplacian]

/-- Joint smoothness on a closed time set gives continuity of each time
slice on that same set, including its endpoints. -/
theorem timeSlice_continuousOn {M : ComplexManifold n} {f : M.Carrier → ℝ → ℝ}
    {I : Set ℝ} (hf : SmoothSpaceTime f I) (x : M.Carrier) :
    ContinuousOn (f x) I := by
  have hv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  have hc := (hf x).continuousOn.comp
    (continuous_const.prodMk continuous_id).continuousOn
    (fun t ht => ⟨mem_extChartAt_target x, ht⟩)
  change ContinuousOn (fun t => f (chartInv x (chartPt x x)) t) I at hc
  simpa only [hv] using hc

/-- The supplied one-sided derivative at zero is sufficient for the
fundamental theorem on every nonnegative finite time interval. -/
theorem potential_eq_integral_P (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt X) : U x t = ∫ s in (0 : ℝ)..t, P x s := by
  have hcU := (timeSlice_continuousOn hf.2.1 x).mono
    (show Set.Icc 0 t ⊆ Set.Ici 0 from fun _ hs => hs.1)
  have hcP := (timeSlice_continuousOn hf.2.2.1 x).mono
    (show Set.Icc 0 t ⊆ Set.Ici 0 from fun _ hs => hs.1)
  have hd : ∀ s ∈ Set.Ioo 0 t, HasDerivWithinAt (U x) (P x s) (Set.Ioi s) s := by
    intro s hs
    exact (hf.2.2.2.2.2.2.2.1 x s hs.1.le).mono
      (fun z hz => hs.1.le.trans hz.le)
  have hi := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht hcU hd
    (hcP.intervalIntegrable_of_Icc ht)
  rw [hf.2.2.2.2.2.2.1 x, sub_zero] at hi
  exact hi.symm

/-- The nonnegative density rho integrates to precisely minus the given
potential; no new potential is chosen. -/
theorem neg_potential_eq_integral_rho (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt X) :
    -U x t = ∫ s in (0 : ℝ)..t, ρ x s := by
  rw [potential_eq_integral_P X o h U P ρ hf ht x, ← intervalIntegral.integral_neg]
  apply intervalIntegral.integral_congr
  intro s hs
  rw [Set.uIcc_of_le ht] at hs
  exact (hf.2.2.2.2.2.2.2.2.2.1 x s hs.1).1.symm

theorem potential_nonpos (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt X) : U x t ≤ 0 := by
  have hn : 0 ≤ -U x t := by
    rw [neg_potential_eq_integral_rho X o h U P ρ hf ht x]
    exact intervalIntegral.integral_nonneg ht
      (fun s hs => (hf.2.2.2.2.2.2.2.2.2.1 x s hs.1).2)
  linarith

/-- The two Loewner bounds in the actual controlled exhaustion bound its
actual complex Laplacian, with the dimension factor retained. -/
theorem controlledExhaustion_laplacian_bounds (X : KahlerManifold n) (o : Pt X)
    (u : Pt X → ℝ) (hu : ControlledExhaustion X o u) :
    ∃ C : ℝ, 0 < C ∧ ∀ x, |laplacian X.metric.form u x| ≤ n * C / u x := by
  obtain ⟨C, hC, hb⟩ := hu.2.2.2
  refine ⟨C, hC, fun x => ?_⟩
  have hg : (gMat X.metric.form x).PosDef :=
    LeafProofs.L18Aux.hMat_posDef X.metric.form x (chartPt x x) (mem_extChartAt_target x)
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

theorem ballIntegralLE_mono_bound {M : ComplexManifold n} (g : HermitianField M)
    (μ : Measure M.Carrier) (o : M.Carrier) (f : M.Carrier → ℝ) (L : ℝ)
    {A B : ℝ} (hA : BallIntegralLE g μ o f L A) (hAB : A ≤ B) :
    BallIntegralLE g μ o f L B :=
  hA.trans (mul_le_mul' (ENNReal.ofReal_le_ofReal hAB) le_rfl)

theorem ballIntegralLE_mono_integrand {M : ComplexManifold n} (g : HermitianField M)
    (μ : Measure M.Carrier) (o : M.Carrier) {f k : M.Carrier → ℝ} (L B : ℝ)
    (hk : BallIntegralLE g μ o k L B) (hfk : ∀ x, f x ≤ k x) :
    BallIntegralLE g μ o f L B :=
  (lintegral_mono (fun x => ENNReal.ofReal_le_ofReal (hfk x))).trans hk

theorem ballIntegralLE_nonneg_smul {M : ComplexManifold n} (g : HermitianField M)
    (μ : Measure M.Carrier) (o : M.Carrier) (f : M.Carrier → ℝ) (L B c : ℝ)
    (hc : 0 ≤ c) (hf : BallIntegralLE g μ o f L B) :
    BallIntegralLE g μ o (fun x => c * f x) L (c * B) := by
  unfold BallIntegralLE at hf ⊢
  simp_rw [ENNReal.ofReal_mul hc]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top, mul_assoc]
  exact mul_le_mul' le_rfl hf

/-- The scalar-curvature sign in the given flow makes its rho monotone
in physical time, including the initial endpoint. -/
theorem rho_monotoneOn (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) (x : Pt X) :
    MonotoneOn (ρ x) (Set.Ici 0) := by
  have hanti : AntitoneOn (P x) (Set.Ici 0) := by
    apply antitoneOn_of_hasDerivWithinAt_nonpos (convex_Ici (0 : ℝ))
      (timeSlice_continuousOn hf.2.2.1 x)
    · intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      exact (hf.2.2.2.2.2.2.2.2.2.2.1 x s hs0).1.mono interior_subset
    · intro s hs
      have hs0 : 0 ≤ s := interior_subset hs
      exact neg_nonpos.mpr (hf.2.2.2.2.2.2.2.2.2.2.1 x s hs0).2
  intro s hs t ht hst
  rw [(hf.2.2.2.2.2.2.2.2.2.1 x s hs).1,
    (hf.2.2.2.2.2.2.2.2.2.1 x t ht).1]
  exact neg_le_neg (hanti hs ht hst)

/-- A pointwise time bound removes any need to exchange space and time
integrals in the potential estimate. -/
theorem neg_potential_le_time_mul_rho (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    {t : ℝ} (ht : 0 ≤ t) (x : Pt X) : -U x t ≤ t * ρ x t := by
  have hci := (timeSlice_continuousOn hf.2.2.2.1 x).mono
    (show Set.Icc 0 t ⊆ Set.Ici 0 from fun _ hs => hs.1)
  rw [neg_potential_eq_integral_rho X o h U P ρ hf ht x]
  have hbound := intervalIntegral.integral_mono_on ht (hci.intervalIntegrable_of_Icc ht)
    (intervalIntegrable_const : IntervalIntegrable (fun _ : ℝ => ρ x t) volume 0 t)
    (fun s hs => rho_monotoneOn X o h U P ρ hf x hs.1 ht hs.2)
  simpa only [intervalIntegral.integral_const, sub_zero, smul_eq_mul] using hbound

/-- The exact potential ball estimate needed after moving the Laplacian
onto a cutoff. Its constant is chosen before every volume, radius and time. -/
theorem neg_potential_ball_average (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ) :
    ∀ T, 0 < T → ∃ C : ℝ, 0 < C ∧ ∀ μ, IsRiemannianVolume X.metric.form μ →
      ∀ L, 1 ≤ L → ∀ t ∈ Set.Icc 0 T,
        BallIntegralLE X.metric.form μ o (fun x => -U x t) L (C * t * L) := by
  intro T hT
  obtain ⟨C₀, hC₀⟩ := hf.2.2.2.2.2.2.2.2.2.2.2.1 T hT.le
  let C := max C₀ 1
  refine ⟨C, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro μ hμ L hL t ht
  have hrho : BallIntegralLE X.metric.form μ o (fun x => ρ x t) L (C * L) :=
    ballIntegralLE_mono_bound _ _ _ _ _ (hC₀ μ hμ L hL t ht)
      (mul_le_mul_of_nonneg_right (le_max_left _ _) (zero_le_one.trans hL))
  have hpot := ballIntegralLE_mono_integrand X.metric.form μ o L (t * (C * L))
    (ballIntegralLE_nonneg_smul X.metric.form μ o (fun x => ρ x t) L (C * L) t ht.1 hrho)
    (neg_potential_le_time_mul_rho X o h U P ρ hf ht.1)
  convert hpot using 1
  ring

/-- The original F02 ball estimate at t=0, for every volume witness. -/
theorem metricDefect_ballIntegral_zero (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (μ : Measure (Pt X)) (L C : ℝ) :
    BallIntegralLE X.metric.form μ o
      (fun x => traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h 0) x))
      L (C * 0 / L) := by
  simp only [BallIntegralLE, metricDefect_zero X o h U P ρ hf, ENNReal.ofReal_zero,
    lintegral_zero, mul_zero, zero_div, zero_mul, le_refl]

end Yau.Proofs.F02Aux
