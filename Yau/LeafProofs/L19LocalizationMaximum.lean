import Yau.LeafProofs.L19LocalizationEvolution
import Yau.LeafProofs.L19LocalizationCutoff

/-! Differential signs at actual local maxima and maxima on compact cylinders. -/

noncomputable section
open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L12Aux L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1800000

theorem second_deriv_nonpos_at_local_max {f : ℝ → ℝ} {t : ℝ}
    (hf : ContinuousAt f t) (hm : IsLocalMax f t) : deriv (deriv f) t ≤ 0 := by
  by_contra h
  have hpos : 0 < deriv (deriv f) t := lt_of_not_ge h
  have hmin := isLocalMin_of_deriv_deriv_pos hpos hm.deriv_eq_zero hf
  have heq : f =ᶠ[𝓝 t] fun _ => f t := by
    filter_upwards [hm, hmin] with s hs hs'
    exact le_antisymm hs hs'
  have hz : deriv (deriv f) t = 0 := by
    rw [heq.deriv.deriv_eq]
    simp
  linarith

theorem secondFDeriv_nonpos_at_local_max
    {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hm : IsLocalMax f z) (v : ComplexVector n) :
    fderiv ℝ (fderiv ℝ f) z v v ≤ 0 := by
  let γ : ℝ → ComplexVector n := fun t => z + t • v
  let φ : ℝ → ℝ := f ∘ γ
  have hγ (t : ℝ) : HasDerivAt γ v t := by
    simpa only [γ, one_smul, id_eq] using ((hasDerivAt_id t).smul_const v).const_add z
  have hγ0 : γ 0 = z := by simp [γ]
  have hφ : ContinuousAt φ 0 := by
    have hc : ContinuousAt f (γ 0) := by simpa only [hγ0] using hf.continuousAt
    exact hc.comp (hγ 0).continuousAt
  have hmax : IsLocalMax φ 0 := by
    have hlim : Tendsto γ (𝓝 0) (𝓝 z) := hγ0 ▸ (hγ 0).continuousAt
    change ∀ᶠ t in 𝓝 0, φ t ≤ φ 0
    simpa only [φ, Function.comp_apply, hγ0] using hlim.eventually hm
  have hderiv : deriv φ =ᶠ[𝓝 0] fun t => fderiv ℝ f (γ t) v := by
    have hnear := (hγ 0).continuousAt.eventually
      (hγ0 ▸ hf.eventually (by norm_num))
    filter_upwards [hnear] with t ht
    exact (ht.differentiableAt (by norm_num) |>.hasFDerivAt.comp_hasDerivAt t (hγ t)).deriv
  have hDf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hline : HasDerivAt (fun t => fderiv ℝ f (γ t) v)
      (fderiv ℝ (fderiv ℝ f) z v v) 0 := by
    have hDf' : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) (γ 0) := by
      simpa only [hγ0] using hDf.hasFDerivAt
    have hcomp := (hDf'.comp_hasDerivAt 0 (hγ 0)).clm_apply (hasDerivAt_const 0 v)
    simpa only [Function.comp_def, hγ0, map_zero, add_zero] using hcomp
  have hsecond : deriv (deriv φ) 0 = fderiv ℝ (fderiv ℝ f) z v v := by
    rw [hderiv.deriv_eq, hline.deriv]
  rw [← hsecond]
  exact second_deriv_nonpos_at_local_max hφ hmax

theorem endpointFrameHessianTrace_nonpos_at_local_max (g : SmoothMetric M) (q : M.Carrier)
    (b : Fin (2 * n) → TangentSpace 𝓘(ℝ, ComplexVector n) q)
    {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hm : IsLocalMax f z) :
    endpointFrameHessianTrace g q b f z ≤ 0 := by
  unfold endpointFrameHessianTrace
  apply Finset.sum_nonpos
  intro i hi
  rw [hm.fderiv_eq_zero]
  simp only [zero_apply, sub_zero]
  exact secondFDeriv_nonpos_at_local_max hf hm _

/-- The time derivative at the last face of a cylinder has the same
nonnegative sign as at an interior positive maximum. -/
theorem hasDerivAt_nonneg_at_left_max {f : ℝ → ℝ} {t d : ℝ}
    (hd : HasDerivAt f d t) (hm : IsLocalMaxOn f (Set.Iic t) t) : 0 ≤ d := by
  have hl := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left (nhdsLT_le_nhdsNE t)
  apply ge_of_tendsto hl
  have hmax : ∀ᶠ s in 𝓝[<] t, f s ≤ f t := by
    have he : ∀ᶠ s in 𝓝[<] t, s ∈ Set.Iic t := by
      filter_upwards [self_mem_nhdsWithin] with s hs
      exact (show s < t from hs).le
    exact (nhdsWithin_le_iff.mpr he) hm
  filter_upwards [hmax, self_mem_nhdsWithin] with s hs hst
  change 0 ≤ (s - t)⁻¹ • (f s - f t)
  change 0 ≤ (s - t)⁻¹ * (f s - f t)
  exact mul_nonneg_of_nonpos_of_nonpos (inv_nonpos.mpr (sub_nonpos.mpr hst.le))
    (sub_nonpos.mpr hs)

/-- All-chart joint smoothness gives continuity in the original product topology. -/
theorem smoothSpaceTime_continuousAt {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    ContinuousAt (fun p : M.Carrier × ℝ => u p.1 p.2) (x, t) := by
  have hmem : (chartPt x x, t) ∈ chartTarget x ×ˢ Set.Ioi (0 : ℝ) :=
    ⟨mem_extChartAt_target x, ht⟩
  have hc : ContinuousAt (fun p : ComplexVector n × ℝ => u (chartInv x p.1) p.2)
      (chartPt x x, t) :=
    ((hu x).contDiffAt (((isOpen_extChartAt_target (I := ComplexModel n) x).prod
      isOpen_Ioi).mem_nhds hmem)).continuousAt
  have hmap : ContinuousAt (fun p : M.Carrier × ℝ => (chartPt x p.1, p.2)) (x, t) :=
    ((continuousAt_extChartAt (I := ComplexModel n) x).comp continuousAt_fst).prodMk
      continuousAt_snd
  have hcomp := hc.comp (f := fun p : M.Carrier × ℝ => (chartPt x p.1, p.2)) hmap
  apply hcomp.congr
  have hfst : Tendsto (fun p : M.Carrier × ℝ => p.1) (𝓝 (x, t)) (𝓝 x) := continuousAt_fst
  have hnear := hfst.eventually
    ((isOpen_extChartAt_source (I := ComplexModel n) x).mem_nhds
      (mem_extChartAt_source x))
  filter_upwards [hnear] with p hp
  exact congrArg (fun y => u y p.2) ((extChartAt (ComplexModel n) x).left_inv hp)

/-- The actual continuous distance cutoff attains a maximum on each
compact closed distance ball and compact time interval. -/
theorem exists_distanceCutoff_cylinder_maximum (g : SmoothMetric M)
    (x : M.Carrier) {R T : ℝ} (hR : 0 < R) (hT : 0 < T)
    {W : M.Carrier → ℝ → ℝ}
    (hW : ContinuousOn (fun p : M.Carrier × ℝ => W p.1 p.2)
      ({y | inducedDistance g.form x y ≤ R} ×ˢ Set.Icc 0 T)) :
    ∃ q : M.Carrier, ∃ s : ℝ,
      inducedDistance g.form x q ≤ R ∧ s ∈ Set.Icc 0 T ∧
      ∀ y : M.Carrier, ∀ t : ℝ, inducedDistance g.form x y ≤ R →
        t ∈ Set.Icc 0 T →
        distanceCutoff g x R y * t * W y t ≤ distanceCutoff g x R q * s * W q s := by
  let K := {y : M.Carrier | inducedDistance g.form x y ≤ R}
  let H : M.Carrier × ℝ → ℝ := fun p => distanceCutoff g x R p.1 * p.2 * W p.1 p.2
  have hη : Continuous (fun p : M.Carrier × ℝ => distanceCutoff g x R p.1) :=
    (distanceCutoff_continuous g x R).comp continuous_fst
  have htime : Continuous (fun p : M.Carrier × ℝ => p.2) := continuous_snd
  have hH : ContinuousOn H (K ×ˢ Set.Icc 0 T) := (hη.mul htime).continuousOn.mul hW
  have hx : x ∈ K := by
    change inducedDistance g.form x x ≤ R
    rw [g.induced_distance_eq_zero.mpr rfl]
    exact hR.le
  have hcompact : IsCompact (K ×ˢ Set.Icc 0 T) :=
    (isCompact_inducedDistance_sublevel g x R).prod isCompact_Icc
  obtain ⟨p, hp, hmax⟩ := hcompact.exists_isMaxOn (f := H) ⟨(x, 0), hx, le_rfl, hT.le⟩ hH
  have hresult : ∀ z : M.Carrier × ℝ, z ∈ K ×ˢ Set.Icc 0 T → H z ≤ H p := hmax
  refine ⟨p.1, p.2, hp.1, hp.2, ?_⟩
  intro y t hy ht
  exact hresult (y, t) ⟨hy, ht⟩

/-- Multiplication by a positive scalar field preserves a touching lower
support at an actual spatial maximum inside the distance ball. -/
theorem lower_support_preserves_space_max (g : SmoothMetric M) (x q : M.Carrier)
    {R : ℝ} (hq : inducedDistance g.form x q < R)
    {η W : M.Carrier → ℝ} (hη : η q = distanceCutoff g x R q)
    (hnear : ∀ᶠ y in 𝓝 q, η y ≤ distanceCutoff g x R y)
    (hW : ContinuousAt W q) (hWpos : 0 < W q)
    (hmax : ∀ y : M.Carrier, inducedDistance g.form x y ≤ R →
      distanceCutoff g x R y * W y ≤ distanceCutoff g x R q * W q) :
    IsLocalMax (fun z => η (chartInv q z) * W (chartInv q z)) (chartPt q q) := by
  have hdist : ∀ᶠ y in 𝓝 q, inducedDistance g.form x y < R :=
    (continuous_distFrom g x).continuousAt.eventually (Iio_mem_nhds hq)
  have hWnear : ∀ᶠ y in 𝓝 q, 0 < W y := hW.eventually (Ioi_mem_nhds hWpos)
  have hm : IsLocalMax (fun y => η y * W y) q := by
    filter_upwards [hdist, hWnear, hnear] with y hyd hyW hyη
    calc
      η y * W y ≤ distanceCutoff g x R y * W y :=
        mul_le_mul_of_nonneg_right hyη hyW.le
      _ ≤ distanceCutoff g x R q * W q := hmax y hyd.le
      _ = η q * W q := by rw [hη]
  have hqinv : chartInv q (chartPt q q) = q :=
    (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)
  have hc : ContinuousAt (chartInv q) (chartPt q q) :=
    continuousAt_extChartAt_symm'' (I := ComplexModel n) (mem_extChartAt_target q)
  have htend : Tendsto (chartInv q) (𝓝 (chartPt q q)) (𝓝 q) := by
    simpa only [hqinv] using hc.tendsto
  change ∀ᶠ z in 𝓝 (chartPt q q), η (chartInv q z) * W (chartInv q z) ≤ _
  simpa only [hqinv] using htend.eventually hm

theorem liYauAuxiliary_time_contDiffAt (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (α τ : ℝ) (x : M.Carrier) {s : ℝ} (ht : 0 < τ + s) :
    ContDiffAt ℝ ∞ (liYauAuxiliary g.form u α τ x) s := by
  have hlog := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have hQ := smoothSpaceTime_time_contDiffAt (smoothSpaceTime_gradNormSq g hlog) x
    (Ioi_mem_nhds ht)
  have hV := smoothSpaceTime_time_contDiffAt (smoothSpaceTime_time_derivative hlog) x
    (Ioi_mem_nhds ht)
  have hmap : ContDiffAt ℝ ∞ (fun r : ℝ => τ + r) s := contDiffAt_const.add contDiffAt_id
  exact contDiffAt_id.mul ((hQ.comp s hmap).sub (contDiffAt_const.mul (hV.comp s hmap)))

theorem liYauAuxiliary_continuousAt (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (α τ : ℝ) (x : M.Carrier) {s : ℝ} (ht : 0 < τ + s) :
    ContinuousAt (fun p : M.Carrier × ℝ => liYauAuxiliary g.form u α τ p.1 p.2) (x, s) := by
  have hlog := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have hQ := smoothSpaceTime_continuousAt (smoothSpaceTime_gradNormSq g hlog) x ht
  have hV := smoothSpaceTime_continuousAt (smoothSpaceTime_time_derivative hlog) x ht
  have hmap : ContinuousAt (fun p : M.Carrier × ℝ => (p.1, τ + p.2)) (x, s) :=
    continuousAt_fst.prodMk (continuousAt_const.add continuousAt_snd)
  have hQc := hQ.comp (f := fun p : M.Carrier × ℝ => (p.1, τ + p.2)) hmap
  have hVc := hV.comp (f := fun p : M.Carrier × ℝ => (p.1, τ + p.2)) hmap
  exact continuousAt_snd.mul (hQc.sub (continuousAt_const.mul hVc))

theorem liYauUnscaled_continuousAt (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (α τ : ℝ) (x : M.Carrier) {s : ℝ} (ht : 0 < τ + s) :
    ContinuousAt (fun p : M.Carrier × ℝ =>
      gradNormSq g.form (fun y => Real.log (u y (τ + p.2))) p.1 -
        α * deriv (fun r => Real.log (u p.1 r)) (τ + p.2)) (x, s) := by
  have hlog := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have hQ := smoothSpaceTime_continuousAt (smoothSpaceTime_gradNormSq g hlog) x ht
  have hV := smoothSpaceTime_continuousAt (smoothSpaceTime_time_derivative hlog) x ht
  have hmap : ContinuousAt (fun p : M.Carrier × ℝ => (p.1, τ + p.2)) (x, s) :=
    continuousAt_fst.prodMk (continuousAt_const.add continuousAt_snd)
  exact (hQ.comp (f := fun p : M.Carrier × ℝ => (p.1, τ + p.2)) hmap).sub
    (continuousAt_const.mul (hV.comp (f := fun p : M.Carrier × ℝ => (p.1, τ + p.2)) hmap))

/-- A maximum for the actual Li--Yau quantity on a genuine compact cylinder. -/
theorem exists_liYauAuxiliary_cylinder_maximum (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (α : ℝ) {τ R T : ℝ} (hτ : 0 < τ) (hR : 0 < R) (hT : 0 < T) (x : M.Carrier) :
    ∃ q : M.Carrier, ∃ s : ℝ,
      inducedDistance g.form x q ≤ R ∧ s ∈ Set.Icc 0 T ∧
      ∀ y : M.Carrier, ∀ t : ℝ, inducedDistance g.form x y ≤ R →
        t ∈ Set.Icc 0 T →
        distanceCutoff g x R y * liYauAuxiliary g.form u α τ y t ≤
          distanceCutoff g x R q * liYauAuxiliary g.form u α τ q s := by
  let W : M.Carrier → ℝ → ℝ := fun y s =>
    gradNormSq g.form (fun z => Real.log (u z (τ + s))) y -
      α * deriv (fun r => Real.log (u y r)) (τ + s)
  have hW : ContinuousOn (fun p : M.Carrier × ℝ => W p.1 p.2)
      ({y | inducedDistance g.form x y ≤ R} ×ˢ Set.Icc 0 T) := by
    intro p hp
    exact (liYauUnscaled_continuousAt g hu α τ p.1
      (add_pos_of_pos_of_nonneg hτ hp.2.1)).continuousWithinAt
  obtain ⟨q, s, hq, hs, hmax⟩ := exists_distanceCutoff_cylinder_maximum g x hR hT hW
  refine ⟨q, s, hq, hs, ?_⟩
  intro y t hy ht
  have hh := hmax y t hy ht
  convert hh using 1 <;> dsimp only [liYauAuxiliary, W] <;> ring

end Yau.LeafProofs.L19Aux
