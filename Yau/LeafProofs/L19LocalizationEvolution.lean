import Yau.LeafProofs.L19Bochner

/-! Ordinary time and spatial differentiation for the localization argument. -/

noncomputable section

open Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder

namespace Yau.LeafProofs.L19Aux

open L18Aux

variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

theorem localSpaceTime_spatial_direction
    {U : Set (ComplexVector n)} (hU : IsOpen U)
    {u : ComplexVector n → ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => u p.1 p.2)
      (U ×ˢ Set.Ioi 0))
    {z : ComplexVector n} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) (i : RIdx n) :
    rDeriv (fun w => u w t) z i =
      fderiv ℝ (fun p : ComplexVector n × ℝ => u p.1 p.2)
        (z, t) (realVec i, 0) := by
  have hmem : (z, t) ∈ U ×ˢ Set.Ioi (0 : ℝ) := ⟨hz, ht⟩
  have hd := (hu.contDiffAt ((hU.prod isOpen_Ioi).mem_nhds hmem)).differentiableAt
    (by simp)
  have hmap : HasFDerivAt (fun w : ComplexVector n => (w, t))
      ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  have hc := congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i))
    (hd.hasFDerivAt.comp z hmap).fderiv
  simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply, rDeriv]
    using hc

theorem localSpaceTime_time_direction
    {U : Set (ComplexVector n)} (hU : IsOpen U)
    {u : ComplexVector n → ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => u p.1 p.2)
      (U ×ˢ Set.Ioi 0))
    {z : ComplexVector n} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) :
    deriv (u z) t =
      fderiv ℝ (fun p : ComplexVector n × ℝ => u p.1 p.2) (z, t) (0, 1) := by
  have hmem : (z, t) ∈ U ×ˢ Set.Ioi (0 : ℝ) := ⟨hz, ht⟩
  have hd := (hu.contDiffAt ((hU.prod isOpen_Ioi).mem_nhds hmem)).differentiableAt
    (by simp)
  have hmap : HasDerivAt (fun s : ℝ => (z, s)) (0, 1) t :=
    (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  simpa only [Function.comp_def] using (hd.hasFDerivAt.comp_hasDerivAt t hmap).deriv

theorem localSpaceTime_spatial_derivative
    {U : Set (ComplexVector n)} (hU : IsOpen U)
    {u : ComplexVector n → ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => u p.1 p.2)
      (U ×ˢ Set.Ioi 0)) (i : RIdx n) :
    ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => rDeriv (fun w => u w p.2) p.1 i)
      (U ×ˢ Set.Ioi 0) := by
  have hD : ContDiffOn ℝ ∞ (fderiv ℝ (fun p : ComplexVector n × ℝ => u p.1 p.2))
      (U ×ˢ Set.Ioi 0) := hu.fderiv_of_isOpen (hU.prod isOpen_Ioi) (by simp)
  apply (hD.clm_apply contDiffOn_const).congr
  intro p hp
  exact localSpaceTime_spatial_direction hU hu hp.1 hp.2 i

theorem localSpaceTime_spatial_time_hasDerivAt
    {U : Set (ComplexVector n)} (hU : IsOpen U)
    {u : ComplexVector n → ℝ → ℝ}
    (hu : ContDiffOn ℝ ∞ (fun p : ComplexVector n × ℝ => u p.1 p.2)
      (U ×ˢ Set.Ioi 0))
    {z : ComplexVector n} (hz : z ∈ U) {t : ℝ} (ht : 0 < t) (i : RIdx n) :
    HasDerivAt (fun s => rDeriv (fun w => u w s) z i)
      (rDeriv (fun w => deriv (u w) t) z i) t := by
  let F : ComplexVector n × ℝ → ℝ := fun p => u p.1 p.2
  have hmem : (z, t) ∈ U ×ˢ Set.Ioi (0 : ℝ) := ⟨hz, ht⟩
  have hF : ContDiffAt ℝ 2 F (z, t) :=
    (hu.contDiffAt ((hU.prod isOpen_Ioi).mem_nhds hmem)).of_le (by simp)
  have hDF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hmapT : HasDerivAt (fun s : ℝ => (z, s)) (0, 1) t :=
    (hasDerivAt_const t z).prodMk (hasDerivAt_id t)
  have hT : HasDerivAt (fun s => fderiv ℝ F (z, s) (realVec i, 0))
      (fderiv ℝ (fderiv ℝ F) (z, t) (0, 1) (realVec i, 0)) t := by
    simpa only [Function.comp_def, map_zero, add_zero] using
      (hDF.hasFDerivAt.comp_hasDerivAt t hmapT).clm_apply
        (hasDerivAt_const t (realVec i, 0))
  have hS : HasFDerivAt (fun w => fderiv ℝ F (w, t) (0, 1))
      (((fderiv ℝ (fderiv ℝ F) (z, t)).comp
        ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0)).flip (0, 1)) z := by
    have hmapS : HasFDerivAt (fun w : ComplexVector n => (w, t))
        ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0) z :=
      (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
    simpa only [Function.comp_def, ContinuousLinearMap.comp_zero, zero_add] using
      (hDF.hasFDerivAt.comp z hmapS).clm_apply (hasFDerivAt_const (0, 1) z)
  have htimeEq : (fun w => deriv (u w) t) =ᶠ[𝓝 z]
      (fun w => fderiv ℝ F (w, t) (0, 1)) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact localSpaceTime_time_direction hU hu hw ht
  have hSpaceValue : rDeriv (fun w => deriv (u w) t) z i =
      fderiv ℝ (fderiv ℝ F) (z, t) (realVec i, 0) (0, 1) := by
    unfold rDeriv
    rw [htimeEq.fderiv_eq, hS.fderiv]
    rfl
  rw [hSpaceValue, hF.isSymmSndFDerivAt (by norm_num) (realVec i, 0) (0, 1)]
  apply hT.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact localSpaceTime_spatial_direction hU hu hz hs i

theorem smoothSpaceTime_second_spatial_time_hasDerivAt
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0)) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) {t : ℝ} (ht : 0 < t)
    (i j : RIdx n) :
    HasDerivAt (fun s => rDeriv (fun w => rDeriv (fun v => u (chartInv a v) s) w j) z i)
      (rDeriv (fun w => rDeriv (fun v => deriv (u (chartInv a v)) t) w j) z i) t := by
  let U := chartTarget a
  have hU : IsOpen U := isOpen_extChartAt_target (I := ComplexModel n) a
  have hD := localSpaceTime_spatial_derivative (u := fun z s => u (chartInv a z) s) hU (hu a) j
  have hd := localSpaceTime_spatial_time_hasDerivAt
    (u := fun w s => rDeriv (fun v => u (chartInv a v) s) w j) hU hD hz ht i
  have heq : (fun w => deriv (fun s => rDeriv (fun v => u (chartInv a v) s) w j) t)
      =ᶠ[𝓝 z] (fun w => rDeriv (fun v => deriv (u (chartInv a v)) t) w j) := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact (smoothSpaceTime_spatial_time_hasDerivAt hu a hw ht j).deriv
  convert hd using 1
  exact congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L (realVec i)) heq.fderiv_eq.symm

/-- A convenient real-Hessian formula for the genuine centered complex operator. -/
theorem laplacian_eq_half_principal (h : HermitianField M)
    {v : M.Carrier → ℝ} (hv : SmoothFn v) (x : M.Carrier) :
    laplacian h v x =
      (∑ i, ∑ j, (realMetricFn h x (chartPt x x))⁻¹ i j *
        rDeriv (fun w => rDeriv (inChart x v) w j) (chartPt x x) i) / 2 := by
  have hf : ContDiffAt ℝ 2 (inChart x v) (chartPt x x) :=
    (contDiffAt_inChart hv x (mem_extChartAt_target x)).of_le (by simp)
  have hh := principal_realLaplacian_eq_twice_traceWith h x (mem_extChartAt_target x) hf
  change (∑ i, ∑ j, (realMetricFn h x (chartPt x x))⁻¹ i j *
    fderiv ℝ (fderiv ℝ (inChart x v)) (chartPt x x) (realVec i) (realVec j)) =
      2 * laplacian h v x at hh
  simp only [rDeriv_rDeriv_eq_hessian hf]
  linarith

/-- The actual fixed-metric Laplacian commutes with ordinary time differentiation. -/
theorem laplacian_time_hasDerivAt (h : HermitianField M)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => laplacian h (fun y => u y s) x)
      (laplacian h (fun y => deriv (u y) t) x) t := by
  let z := chartPt x x
  let A : Matrix (RIdx n) (RIdx n) ℝ := (realMetricFn h x z)⁻¹
  let V : RIdx n → RIdx n → ℝ → ℝ := fun i j s =>
    rDeriv (fun w => rDeriv (inChart x (fun y => u y s)) w j) z i
  let DV : RIdx n → RIdx n → ℝ := fun i j =>
    rDeriv (fun w => rDeriv (inChart x (fun y => deriv (u y) t)) w j) z i
  have hd (i j : RIdx n) : HasDerivAt (V i j) (DV i j) t :=
    smoothSpaceTime_second_spatial_time_hasDerivAt hu x (mem_extChartAt_target x) ht i j
  have hsum : HasDerivAt (fun s => ∑ i, ∑ j, A i j * V i j s)
      (∑ i, ∑ j, A i j * DV i j) t := by
    have hinner (i : RIdx n) : HasDerivAt (fun s => ∑ j, A i j * V i j s)
        (∑ j, A i j * DV i j) t := by
      simpa only [Finset.sum_fn] using HasDerivAt.sum (u := Finset.univ)
        (fun j _ => (hd i j).const_mul (A i j))
    simpa only [Finset.sum_fn] using HasDerivAt.sum (u := Finset.univ)
      (fun i _ => hinner i)
  rw [laplacian_eq_half_principal h
    (smoothSpaceTime_slice (smoothSpaceTime_time_derivative hu) ht) x]
  apply (hsum.div_const 2).congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact laplacian_eq_half_principal h (smoothSpaceTime_slice hu hs) x

/-- The differentiated logarithmic heat equation, with an ordinary second time derivative. -/
theorem positiveHeatSolution_log_time_derivative_hasDerivAt (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => deriv (fun r => Real.log (u x r)) s)
      (laplacian g.form (fun y => deriv (fun r => Real.log (u y r)) t) x +
        scalarGradientPair g.form (fun y => Real.log (u y t))
          (fun y => deriv (fun r => Real.log (u y r)) t) x) t := by
  have hf := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have hd := (laplacian_time_hasDerivAt g.form hf x ht).add
    (gradNormSq_time_hasDerivAt g.form hf x ht)
  apply hd.congr_of_eventuallyEq
  filter_upwards [Ioi_mem_nhds ht] with s hs
  exact positiveHeatSolution_log_equation g.form hu x hs

/-- The exact complex curvature-dimension inequality used by the local maximum argument. -/
def ComplexCD (g : SmoothMetric M) : Prop :=
  ∀ f : M.Carrier → ℝ, SmoothFn f → ∀ x : M.Carrier,
    (laplacian g.form (fun y => gradNormSq g.form f y) x -
      scalarGradientPair g.form f (fun y => laplacian g.form f y) x) ≥
        (laplacian g.form f x) ^ 2 / (n : ℝ)

theorem scalarGradientPair_add_right (h : HermitianField M) (f : M.Carrier → ℝ)
    {u v : M.Carrier → ℝ} (hu : SmoothFn u) (hv : SmoothFn v) (x : M.Carrier) :
    scalarGradientPair h f (fun y => u y + v y) x =
      scalarGradientPair h f u x + scalarGradientPair h f v x := by
  have hdu : DifferentiableAt ℝ (inChart x u) (chartPt x x) :=
    (contDiffAt_inChart hu x (mem_extChartAt_target x)).differentiableAt (by simp)
  have hdv : DifferentiableAt ℝ (inChart x v) (chartPt x x) :=
    (contDiffAt_inChart hv x (mem_extChartAt_target x)).differentiableAt (by simp)
  simp only [scalarGradientPair, chartGradientPair_eq_sum]
  have hD (i : RIdx n) : rDeriv (inChart x (fun y => u y + v y)) (chartPt x x) i =
      rDeriv (inChart x u) (chartPt x x) i + rDeriv (inChart x v) (chartPt x x) i := by
    unfold rDeriv
    change fderiv ℝ (fun w => inChart x u w + inChart x v w) (chartPt x x) (realVec i) = _
    rw [fderiv_fun_add hdu hdv]
    rfl
  simp only [hD, mul_add, Finset.sum_add_distrib]

theorem secondFDeriv_add_local {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {f k : E → ℝ} {z : E} (hf : ContDiffAt ℝ 2 f z) (hk : ContDiffAt ℝ 2 k z)
    (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y => f y + k y)) z v w =
      fderiv ℝ (fderiv ℝ f) z v w + fderiv ℝ (fderiv ℝ k) z v w := by
  have hdf := (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hdk := (hk.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y => f y + k y) =ᶠ[𝓝 z]
      (fun y => fderiv ℝ f y + fderiv ℝ k y) := by
    filter_upwards [hf.eventually (by norm_num), hk.eventually (by norm_num)] with y hy hy'
    exact fderiv_fun_add (hy.differentiableAt (by norm_num)) (hy'.differentiableAt (by norm_num))
  rw [heq.fderiv_eq, fderiv_fun_add hdf hdk]
  rfl

theorem laplacian_add (h : HermitianField M) {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) (x : M.Carrier) :
    laplacian h (fun y => u y + v y) x = laplacian h u x + laplacian h v x := by
  have hf : ContDiffAt ℝ 2 (inChart x u) (chartPt x x) :=
    (contDiffAt_inChart hu x (mem_extChartAt_target x)).of_le (by simp)
  have hk : ContDiffAt ℝ 2 (inChart x v) (chartPt x x) :=
    (contDiffAt_inChart hv x (mem_extChartAt_target x)).of_le (by simp)
  have huv : SmoothFn (fun y => u y + v y) := fun a => (hu a).add (hv a)
  rw [laplacian_eq_half_principal h huv x,
    laplacian_eq_half_principal h hu x, laplacian_eq_half_principal h hv x]
  have hfadd : ContDiffAt ℝ 2 (inChart x (fun y => u y + v y)) (chartPt x x) := hf.add hk
  simp only [rDeriv_rDeriv_eq_hessian hfadd, rDeriv_rDeriv_eq_hessian hf,
    rDeriv_rDeriv_eq_hessian hk]
  change (∑ i, ∑ j, (realMetricFn h x (chartPt x x))⁻¹ i j *
    fderiv ℝ (fderiv ℝ (fun y => inChart x u y + inChart x v y)) (chartPt x x)
      (realVec i) (realVec j)) / 2 = _
  simp only [secondFDeriv_add_local hf hk, mul_add, Finset.sum_add_distrib, add_div]

theorem laplacian_const_mul (h : HermitianField M) {u : M.Carrier → ℝ}
    (hu : SmoothFn u) (c : ℝ) (x : M.Carrier) :
    laplacian h (fun y => c * u y) x = c * laplacian h u x := by
  have hh := laplacian_mul h (smoothFn_const c) hu x
  have hz : chartGradientPair h x (inChart x (fun _ => c)) (inChart x u) (chartPt x x) = 0 := by
    change chartGradientPair h x (fun _ => c) (inChart x u) (chartPt x x) = 0
    simp [chartGradientPair_eq_sum, rDeriv]
  rw [laplacian_const, hz] at hh
  simpa only [mul_zero, add_zero] using hh

/-- The ordinary log-time derivative solves the exact drift heat equation. -/
theorem positiveHeatSolution_log_time_drift (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    laplacian g.form (fun y => deriv (fun r => Real.log (u y r)) t) x -
      deriv (fun s => deriv (fun r => Real.log (u x r)) s) t +
        scalarGradientPair g.form (fun y => Real.log (u y t))
          (fun y => deriv (fun r => Real.log (u y r)) t) x = 0 := by
  rw [(positiveHeatSolution_log_time_derivative_hasDerivAt g hu x ht).deriv]
  ring

/-- Applying the true curvature-dimension inequality to the log heat
energy gives its ordinary parabolic drift inequality. -/
theorem positiveHeatSolution_log_energy_drift (g : SmoothMetric M) (hCD : ComplexCD g)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (x : M.Carrier) {t : ℝ} (ht : 0 < t) :
    laplacian g.form (fun y => gradNormSq g.form (fun z => Real.log (u z t)) y) x -
      deriv (fun s => gradNormSq g.form (fun y => Real.log (u y s)) x) t +
        scalarGradientPair g.form (fun y => Real.log (u y t))
          (fun y => gradNormSq g.form (fun z => Real.log (u z t)) y) x ≥
        laplacian g.form (fun y => Real.log (u y t)) x ^ 2 / (n : ℝ) := by
  have hf := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have hlog := smoothSpaceTime_slice hf ht
  have hQ := smoothSpaceTime_slice (smoothSpaceTime_gradNormSq g hf) ht
  have hL := smoothSpaceTime_slice (positiveHeatSolution_log_laplacian_smoothSpaceTime g hu) ht
  have heq : (fun y => deriv (fun r => Real.log (u y r)) t) =
      (fun y => laplacian g.form (fun z => Real.log (u z t)) y +
        gradNormSq g.form (fun z => Real.log (u z t)) y) :=
    funext (fun y => positiveHeatSolution_log_equation g.form hu y ht)
  rw [(gradNormSq_time_hasDerivAt g.form hf x ht).deriv, heq,
    scalarGradientPair_add_right g.form _ hL hQ x]
  have hh := hCD _ hlog x
  linarith

theorem scalarGradientPair_const_mul_right (h : HermitianField M) (f : M.Carrier → ℝ)
    {u : M.Carrier → ℝ} (hu : SmoothFn u) (c : ℝ) (x : M.Carrier) :
    scalarGradientPair h f (fun y => c * u y) x = c * scalarGradientPair h f u x := by
  have hd : DifferentiableAt ℝ (inChart x u) (chartPt x x) :=
    (contDiffAt_inChart hu x (mem_extChartAt_target x)).differentiableAt (by simp)
  have hD (i : RIdx n) : rDeriv (inChart x (fun y => c * u y)) (chartPt x x) i =
      c * rDeriv (inChart x u) (chartPt x x) i := rDeriv_const_mul hd c i
  simp only [scalarGradientPair, chartGradientPair_eq_sum, hD, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  ring

theorem laplacian_linear_combination (h : HermitianField M) {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) (a b : ℝ) (x : M.Carrier) :
    laplacian h (fun y => a * u y + b * v y) x =
      a * laplacian h u x + b * laplacian h v x := by
  have hau : SmoothFn (fun y => a * u y) := fun z => contDiffOn_const.mul (hu z)
  have hbv : SmoothFn (fun y => b * v y) := fun z => contDiffOn_const.mul (hv z)
  rw [laplacian_add h hau hbv x, laplacian_const_mul h hu a x,
    laplacian_const_mul h hv b x]

theorem scalarGradientPair_linear_combination_right (h : HermitianField M)
    (f : M.Carrier → ℝ) {u v : M.Carrier → ℝ}
    (hu : SmoothFn u) (hv : SmoothFn v) (a b : ℝ) (x : M.Carrier) :
    scalarGradientPair h f (fun y => a * u y + b * v y) x =
      a * scalarGradientPair h f u x + b * scalarGradientPair h f v x := by
  have hau : SmoothFn (fun y => a * u y) := fun z => contDiffOn_const.mul (hu z)
  have hbv : SmoothFn (fun y => b * v y) := fun z => contDiffOn_const.mul (hv z)
  rw [scalarGradientPair_add_right h f hau hbv x,
    scalarGradientPair_const_mul_right h f hu a x,
    scalarGradientPair_const_mul_right h f hv b x]

/-- The actual scaled strict-coefficient log-heat quantity, with a
strictly positive starting time left explicit. -/
def liYauAuxiliary (h : HermitianField M) (u : M.Carrier → ℝ → ℝ)
    (α τ : ℝ) (x : M.Carrier) (s : ℝ) : ℝ :=
  s * (gradNormSq h (fun y => Real.log (u y (τ + s))) x -
    α * deriv (fun r => Real.log (u x r)) (τ + s))

theorem liYauAuxiliary_slice (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (α τ s : ℝ) (ht : 0 < τ + s) :
    SmoothFn (fun y => liYauAuxiliary g.form u α τ y s) := by
  have hlog := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have hQ := smoothSpaceTime_slice (smoothSpaceTime_gradNormSq g hlog) ht
  have hV := smoothSpaceTime_slice (smoothSpaceTime_time_derivative hlog) ht
  intro a
  exact contDiffOn_const.mul ((hQ a).sub (contDiffOn_const.mul (hV a)))

/-- The genuine scaled quantity satisfies the differential inequality
used at a positive local maximum. -/
theorem liYauAuxiliary_drift_of_CD (g : SmoothMetric M) (hn : 0 < n) (hCD : ComplexCD g)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    {α τ s : ℝ} (hα : 1 < α) (hτ : 0 ≤ τ) (hs : 0 < s) (x : M.Carrier) :
    laplacian g.form (fun y => liYauAuxiliary g.form u α τ y s) x -
      deriv (liYauAuxiliary g.form u α τ x) s +
        scalarGradientPair g.form (fun y => Real.log (u y (τ + s)))
          (fun y => liYauAuxiliary g.form u α τ y s) x ≥
      (liYauAuxiliary g.form u α τ x s + (α - 1) * s *
        gradNormSq g.form (fun y => Real.log (u y (τ + s))) x) ^ 2 /
          ((n : ℝ) * α ^ 2 * s) - liYauAuxiliary g.form u α τ x s / s := by
  let t := τ + s
  let f : M.Carrier → ℝ := fun y => Real.log (u y t)
  let Q : M.Carrier → ℝ := fun y => gradNormSq g.form f y
  let V : M.Carrier → ℝ := fun y => deriv (fun r => Real.log (u y r)) t
  let DQ := deriv (fun r => gradNormSq g.form (fun y => Real.log (u y r)) x) t
  let DV := deriv (fun r => deriv (fun v => Real.log (u x v)) r) t
  have ht : 0 < t := add_pos_of_nonneg_of_pos hτ hs
  have hlog := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have hQ : SmoothFn Q := smoothSpaceTime_slice (smoothSpaceTime_gradNormSq g hlog) ht
  have hV : SmoothFn V := smoothSpaceTime_slice (smoothSpaceTime_time_derivative hlog) ht
  have hspace : (fun y => liYauAuxiliary g.form u α τ y s) =
      (fun y => s * Q y + (-s * α) * V y) := by
    funext y
    dsimp [liYauAuxiliary, Q, V, f, t]
    ring
  have hL : laplacian g.form (fun y => liYauAuxiliary g.form u α τ y s) x =
      s * laplacian g.form Q x + (-s * α) * laplacian g.form V x := by
    rw [hspace, laplacian_linear_combination g.form hQ hV]
  have hP : scalarGradientPair g.form f
      (fun y => liYauAuxiliary g.form u α τ y s) x =
      s * scalarGradientPair g.form f Q x + (-s * α) * scalarGradientPair g.form f V x := by
    rw [hspace, scalarGradientPair_linear_combination_right g.form f hQ hV]
  have hDQ : HasDerivAt (fun r => gradNormSq g.form (fun y => Real.log (u y r)) x) DQ t := by
    have hd := gradNormSq_time_hasDerivAt g.form hlog x ht
    simpa only [DQ, hd.deriv] using hd
  have hDV : HasDerivAt (fun r => deriv (fun v => Real.log (u x v)) r) DV t := by
    have hd := positiveHeatSolution_log_time_derivative_hasDerivAt g hu x ht
    simpa only [DV, hd.deriv] using hd
  have htime : deriv (liYauAuxiliary g.form u α τ x) s =
      (Q x - α * V x) + s * (DQ - α * DV) := by
    have hmap : HasDerivAt (fun r : ℝ => τ + r) 1 s := (hasDerivAt_id s).const_add τ
    have hdQ := hDQ.comp s hmap
    have hdV := hDV.comp s hmap
    have hd := (hasDerivAt_id s).mul (hdQ.sub (hdV.const_mul α))
    convert hd.deriv using 1
    · rfl
    · change Q x - α * V x + s * (DQ - α * DV) =
        1 * (Q x - α * V x) + s * (DQ * 1 - α * (DV * 1))
      ring
  have henergy := positiveHeatSolution_log_energy_drift g hCD hu x ht
  have htimeeq := positiveHeatSolution_log_time_drift g hu x ht
  change laplacian g.form Q x - DQ + scalarGradientPair g.form f Q x ≥
    laplacian g.form f x ^ 2 / (n : ℝ) at henergy
  change laplacian g.form V x - DV + scalarGradientPair g.form f V x = 0 at htimeeq
  have hmain : laplacian g.form (fun y => liYauAuxiliary g.form u α τ y s) x -
      deriv (liYauAuxiliary g.form u α τ x) s +
        scalarGradientPair g.form f (fun y => liYauAuxiliary g.form u α τ y s) x ≥
      s * (laplacian g.form f x ^ 2 / (n : ℝ)) - (Q x - α * V x) := by
    rw [hL, hP, htime]
    have he := mul_le_mul_of_nonneg_left henergy hs.le
    have hz := congrArg (fun a : ℝ => (-s * α) * a) htimeeq
    nlinarith only [he, hz]
  have hpde : V x = laplacian g.form f x + Q x :=
    positiveHeatSolution_log_equation g.form hu x ht
  have hα0 : α ≠ 0 := (lt_trans zero_lt_one hα).ne'
  have hn0 : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
  have hval : liYauAuxiliary g.form u α τ x s = s * (Q x - α * V x) := rfl
  have hrhs :
      (liYauAuxiliary g.form u α τ x s + (α - 1) * s * Q x) ^ 2 /
        ((n : ℝ) * α ^ 2 * s) - liYauAuxiliary g.form u α τ x s / s =
      s * (laplacian g.form f x ^ 2 / (n : ℝ)) - (Q x - α * V x) := by
    rw [hval, hpde]
    field_simp
    <;> ring
  change _ ≥ (liYauAuxiliary g.form u α τ x s + (α - 1) * s * Q x) ^ 2 /
    ((n : ℝ) * α ^ 2 * s) - liYauAuxiliary g.form u α τ x s / s
  rw [hrhs]
  exact hmain

end Yau.LeafProofs.L19Aux
