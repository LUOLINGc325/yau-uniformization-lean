import Yau.LeafProofs.L18

/-!
Calculus for the frozen Li--Yau leaf. The heat equation, logarithm, and
gradient below are the project's actual operators. No source theorem or
heat-kernel minimality is assumed.
-/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Joint smoothness gives a genuinely smooth spatial slice. -/
theorem smoothSpaceTime_slice {u : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hu : SmoothSpaceTime u I) {t : ℝ} (ht : t ∈ I) :
    SmoothFn (fun x => u x t) := by
  intro a
  exact (hu a).comp (contDiffOn_id.prodMk contDiffOn_const)
    (fun z hz => ⟨hz, ht⟩)

/-- At an interior time the time slice is ordinarily smooth, rather than
only smooth with respect to a closed or one-sided time domain. -/
theorem smoothSpaceTime_time_contDiffAt {u : M.Carrier → ℝ → ℝ} {I : Set ℝ}
    (hu : SmoothSpaceTime u I) (x : M.Carrier) {t : ℝ} (ht : I ∈ 𝓝 t) :
    ContDiffAt ℝ ∞ (u x) t := by
  have hchart : chartTarget x ∈ 𝓝 (chartPt x x) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_target x)
  have h := (hu x).contDiffAt (prod_mem_nhds hchart ht)
  have hmap : ContDiffAt ℝ ∞ (fun s : ℝ => (chartPt x x, s)) t :=
    contDiffAt_const.prodMk contDiffAt_id
  have hv : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  simpa only [Function.comp_def, hv] using h.comp t hmap

theorem positiveHeatSolution_slice (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    {t : ℝ} (ht : 0 < t) : SmoothFn (fun x => u x t) :=
  smoothSpaceTime_slice hu.1 ht

/-- The original PDE equality has its genuine ordinary derivative witness. -/
theorem positiveHeatSolution_hasDerivAt (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (u x) (laplacian h (fun y => u y t) x) t := by
  have hd := (smoothSpaceTime_time_contDiffAt hu.1 x (Ioi_mem_nhds ht)).differentiableAt
    (by simp)
  rw [← (hu.2 x t ht).2]
  exact hd.hasDerivAt

theorem positiveHeatSolution_log_smoothSpaceTime (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u) :
    SmoothSpaceTime (fun x t => Real.log (u x t)) (Set.Ioi 0) := by
  intro a
  exact (hu.1 a).log (fun p hp => (hu.2 (chartInv a p.1) p.2 hp.2).1.ne')

theorem positiveHeatSolution_log_slice (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    {t : ℝ} (ht : 0 < t) : SmoothFn (fun x => Real.log (u x t)) :=
  smoothSpaceTime_slice (positiveHeatSolution_log_smoothSpaceTime h hu) ht

theorem positiveHeatSolution_log_hasDerivAt (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => Real.log (u x s))
      (laplacian h (fun y => u y t) x / u x t) t :=
  (positiveHeatSolution_hasDerivAt h hu x ht).log (hu.2 x t ht).1.ne'

/-- Logarithmic energy uses the actual project gradient, including its
complex normalization. -/
theorem gradNormSq_log (h : HermitianField M) {v : M.Carrier → ℝ}
    (hv : SmoothFn v) (hpos : ∀ x, 0 < v x) (x : M.Carrier) :
    gradNormSq h (fun y => Real.log (v y)) x = gradNormSq h v x / v x ^ 2 := by
  have hlog : SmoothFn (fun y => Real.log (v y)) := by
    intro a
    exact (hv a).log (fun z hz => (hpos (chartInv a z)).ne')
  have henergy := scalarGradientPair_scalar_comp_self h hv Real.log x
    (Real.differentiableAt_log (hpos x).ne')
  rw [scalarGradientPair_eq_twice_gradNormSq h hlog x,
    scalarGradientPair_eq_twice_gradNormSq h hv x, Real.deriv_log] at henergy
  have hsq : (v x)⁻¹ ^ 2 * gradNormSq h v x = gradNormSq h v x / v x ^ 2 := by
    rw [div_eq_mul_inv, inv_pow]
    ring
  nlinarith [henergy]

theorem laplacian_log (h : HermitianField M) {v : M.Carrier → ℝ}
    (hv : SmoothFn v) (hpos : ∀ x, 0 < v x) (x : M.Carrier) :
    laplacian h (fun y => Real.log (v y)) x =
      laplacian h v x / v x - gradNormSq h v x / v x ^ 2 := by
  have hchain := laplacian_scalar_comp h hv Real.log x
    (Real.contDiffAt_log.mpr (hpos x).ne')
  rw [Real.deriv_log, Real.deriv_log', deriv_inv,
    scalarGradientPair_eq_twice_gradNormSq h hv x] at hchain
  rw [hchain]
  simp only [div_eq_mul_inv]
  ring

/-- The positive heat equation becomes the precise nonlinear logarithmic
heat equation required by the Li--Yau argument. -/
theorem positiveHeatSolution_log_equation (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    deriv (fun s => Real.log (u x s)) t =
      laplacian h (fun y => Real.log (u y t)) x +
        gradNormSq h (fun y => Real.log (u y t)) x := by
  rw [(positiveHeatSolution_log_hasDerivAt h hu x ht).deriv,
    laplacian_log h (positiveHeatSolution_slice h hu ht) (fun y => (hu.2 y t ht).1) x,
    gradNormSq_log h (positiveHeatSolution_slice h hu ht) (fun y => (hu.2 y t ht).1) x]
  ring

/-- The Li--Yau quantity is exactly minus the logarithmic Laplacian. -/
theorem positiveHeatSolution_liYauQuantity (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    gradNormSq h (fun y => Real.log (u y t)) x -
      deriv (fun s => Real.log (u x s)) t =
        -laplacian h (fun y => Real.log (u y t)) x := by
  rw [positiveHeatSolution_log_equation h hu x ht]
  ring

/-- Nonnegative positive-time translations retain the original heat
equation and the original all-chart regularity. -/
theorem positiveHeatSolution_time_translate (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    LeafCandidates.PositiveHeatSolution h (fun x t => u x (t + τ)) := by
  constructor
  · intro a
    exact (hu.1 a).comp
      (contDiffOn_fst.prodMk (contDiffOn_snd.add contDiffOn_const))
      (fun p hp => ⟨hp.1, add_pos_of_pos_of_nonneg hp.2 hτ⟩)
  · intro x t ht
    have htime : 0 < t + τ := by linarith
    refine ⟨(hu.2 x (t + τ) htime).1, ?_⟩
    have hd := (positiveHeatSolution_hasDerivAt h hu x htime).comp t
      ((hasDerivAt_id t).add_const τ)
    simpa only [Function.comp_def, id_eq, mul_one] using hd.deriv

/-- Adding a nonnegative constant gives the genuine positive translates
used when applying a logarithmic differential estimate. -/
theorem positiveHeatSolution_add_const (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution h u)
    {c : ℝ} (hc : 0 ≤ c) :
    LeafCandidates.PositiveHeatSolution h (fun x t => u x t + c) := by
  constructor
  · intro a
    exact (hu.1 a).add contDiffOn_const
  · intro x t ht
    refine ⟨add_pos_of_pos_of_nonneg (hu.2 x t ht).1 hc, ?_⟩
    rw [laplacian_add_const h (positiveHeatSolution_slice h hu ht) c x]
    exact ((positiveHeatSolution_hasDerivAt h hu x ht).add_const c).deriv

/-- Doubling the project time yields a solution of the independently
computed real Levi--Civita heat equation. Its generator is displayed rather
than supplied as independent analytic data. -/
theorem positiveHeatSolution_real_time_change (g : SmoothMetric M) (hK : IsKahler g)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (x : M.Carrier) {s : ℝ} (hs : 0 < s) :
    HasDerivAt (fun r => u x (2 * r))
      (∑ a, ∑ b, (realMetricFn g.form x (chartPt x x))⁻¹ a b *
        (rDeriv (fun w => rDeriv (inChart x (fun y => u y (2 * s))) w b)
            (chartPt x x) a -
          ∑ c, christoffel g.form x (chartPt x x) c a b *
            rDeriv (inChart x (fun y => u y (2 * s))) (chartPt x x) c)) s := by
  have htime : 0 < 2 * s := by positivity
  rw [kahler_realLaplacian_center g hK (positiveHeatSolution_slice g.form hu htime) x]
  have hd := (positiveHeatSolution_hasDerivAt g.form hu x htime).comp s
    ((hasDerivAt_id s).const_mul 2)
  simpa only [Function.comp_def, mul_one, one_mul, mul_comm] using hd

/-- The empty complex index set makes the computed scalar Laplacian zero. -/
theorem laplacian_dim_zero {M : ComplexManifold 0} (h : HermitianField M)
    (v : M.Carrier → ℝ) (x : M.Carrier) : laplacian h v x = 0 := by
  simp [laplacian, traceWith, Matrix.trace]

/-- The original differential target includes complex dimension zero. -/
theorem positiveHeatSolution_liYau_dim_zero {M : ComplexManifold 0}
    (h : HermitianField M) {u : M.Carrier → ℝ → ℝ}
    (hu : LeafCandidates.PositiveHeatSolution h u) (x : M.Carrier)
    {t : ℝ} (ht : 0 < t) :
    gradNormSq h (fun y => Real.log (u y t)) x -
      deriv (fun s => Real.log (u x s)) t ≤ (0 : ℝ) / t := by
  rw [positiveHeatSolution_liYauQuantity h hu x ht, laplacian_dim_zero]
  simp

end Yau.LeafProofs.L19Aux
