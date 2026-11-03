import Yau.LeafProofs.L19OrthonormalTrace
import Yau.LeafProofs.L19EndpointEnergySupport

/-! Integrating the original logarithmic differential estimate along
actual minimizing geodesics, with the project's heat normalization. -/

noncomputable section

open MeasureTheory Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder InnerProductSpace

namespace Yau.LeafProofs.L19Aux

set_option maxHeartbeats 1800000
set_option backward.isDefEq.respectTransparency false

open L18Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- The true joint differential splits into the ordinary spatial and
time derivatives, for an arbitrary real spatial direction. -/
theorem smoothSpaceTime_split_fderiv {u : M.Carrier → ℝ → ℝ}
    (hu : SmoothSpaceTime u (Set.Ioi 0)) (a : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a) {t : ℝ} (ht : 0 < t)
    (v : ComplexVector n) (b : ℝ) :
    fderiv ℝ (fun p : ComplexVector n × ℝ => u (chartInv a p.1) p.2)
      (z, t) (v, b) =
        fderiv ℝ (inChart a (fun x => u x t)) z v + b * deriv (u (chartInv a z)) t := by
  let F : ComplexVector n × ℝ → ℝ := fun p => u (chartInv a p.1) p.2
  have hO : IsOpen (chartTarget a ×ˢ Set.Ioi (0 : ℝ)) :=
    (isOpen_extChartAt_target (I := ComplexModel n) a).prod isOpen_Ioi
  have hmem : (z, t) ∈ chartTarget a ×ˢ Set.Ioi (0 : ℝ) := ⟨hz, ht⟩
  have hF : DifferentiableAt ℝ F (z, t) :=
    ((hu a).contDiffAt (hO.mem_nhds hmem)).differentiableAt (by simp)
  have hmap : HasFDerivAt (fun w : ComplexVector n => (w, t))
      ((ContinuousLinearMap.id ℝ (ComplexVector n)).prod 0) z :=
    (hasFDerivAt_id z).prodMk (hasFDerivAt_const t z)
  have hspatial : fderiv ℝ (inChart a (fun x => u x t)) z v =
      fderiv ℝ F (z, t) (v, 0) := by
    change fderiv ℝ (fun w => u (chartInv a w) t) z v = _
    simpa only [Function.comp_def, ContinuousLinearMap.comp_apply,
      ContinuousLinearMap.prod_apply, ContinuousLinearMap.id_apply, zero_apply, F, inChart]
      using congrArg (fun L : ComplexVector n →L[ℝ] ℝ => L v)
        (hF.hasFDerivAt.comp z hmap).fderiv
  have hsplit : (v, b) = (v, 0) + b • (0, 1) := by ext <;> simp
  change fderiv ℝ F (z, t) (v, b) = _
  rw [hsplit, map_add, map_smul, ← hspatial]
  rw [show fderiv ℝ F (z, t) (0, 1) = deriv (u (chartInv a z)) t from
    (smoothSpaceTime_time_direction hu a hz ht).symm]
  rfl

/-- The spatial coordinate differential is the actual manifold
differential evaluated at the same genuine tangent vector. -/
theorem scalar_fderiv_realTangentCoords {f : M.Carrier → ℝ} (hf : SmoothFn f)
    (x : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    fderiv ℝ (inChart x f) (chartPt x x) (L12Aux.realTangentCoords x x v) =
      mvfderiv 𝓘(ℝ, ComplexVector n) f x v := by
  have hp := scalar_mvfderiv_centeredFrame hf x (L12Aux.realTangentCoords x x v)
  rw [← realFrameCLM_eq_centeredRealFrame,
    L12Aux.realFrameCLM_realTangentCoords x x (mem_chart_source _ _)] at hp
  exact hp.symm

/-- The actual scalar differential obeys the physical gradient bound at
each point; the tangent norm is the true `2 Re h` norm. -/
theorem scalarDifferential_norm_le_gradient (h : HermitianField M)
    {f : M.Carrier → ℝ} (hf : SmoothFn f) (x : M.Carrier)
    (v : TangentSpace 𝓘(ℝ, ComplexVector n) x) :
    letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
    letI := L12Aux.underlyingRealTangentInnerProductSpace h x
    ‖mvfderiv 𝓘(ℝ, ComplexVector n) f x v‖ ≤
      Real.sqrt (scalarGradientPair h f f x) * ‖v‖ := by
  letI := L12Aux.underlyingRealTangentNormedAddCommGroup h x
  letI := L12Aux.underlyingRealTangentInnerProductSpace h x
  have hnorm : ‖mvfderiv 𝓘(ℝ, ComplexVector n) f x‖ =
      Real.sqrt (scalarGradientPair h f f x) := by
    rw [scalarGradientPair_eq_realDifferential_opNorm_sq h hf x]
    exact (Real.sqrt_sq (ContinuousLinearMap.opNorm_nonneg _)).symm
  calc
    _ ≤ ‖mvfderiv 𝓘(ℝ, ComplexVector n) f x‖ * ‖v‖ := ContinuousLinearMap.le_opNorm _ _
    _ = _ := by rw [hnorm]

/-- Joint differentiation along the actual geodesic flow and an ordinary
time parametrization.  No coordinate velocity is supplied as a hypothesis. -/
theorem smoothSpaceTime_geodesic_hasDerivAt (g : SmoothMetric M)
    {u : M.Carrier → ℝ → ℝ} (hu : SmoothSpaceTime u (Set.Ioi 0))
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    {T : ℝ → ℝ} {θ b : ℝ} (hT : HasDerivAt T b θ) (ht : 0 < T θ) :
    letI := L12Aux.manifold_realSmooth M
    HasDerivAt (fun s => u (L12Aux.realGeodesicFlow g p s).proj (T s))
      (mvfderiv 𝓘(ℝ, ComplexVector n) (fun x => u x (T θ))
        (L12Aux.realGeodesicFlow g p θ).proj (L12Aux.realGeodesicFlow g p θ).2 +
        b * deriv (u (L12Aux.realGeodesicFlow g p θ).proj) (T θ)) θ := by
  letI := L12Aux.manifold_realSmooth M
  let γ := L12Aux.realGeodesicFlow g p
  let a := (γ θ).proj
  let z := chartPt a a
  have hz : z ∈ chartTarget a := mem_extChartAt_target a
  have hmem : (z, T θ) ∈ chartTarget a ×ˢ Set.Ioi (0 : ℝ) := ⟨hz, ht⟩
  have hcoord := L12Aux.realGeodesicFlow_baseCoords_hasDerivAt g p θ
  have hF : DifferentiableAt ℝ
      (fun q : ComplexVector n × ℝ => u (chartInv a q.1) q.2) (z, T θ) :=
    ((hu a).contDiffAt (((isOpen_extChartAt_target (I := ComplexModel n) a).prod
      isOpen_Ioi).mem_nhds hmem)).differentiableAt (by simp)
  have hc := hF.hasFDerivAt.comp_hasDerivAt θ (hcoord.prodMk hT)
  have hinv : chartInv a z = a := (extChartAt (ComplexModel n) a).left_inv
    (mem_extChartAt_source a)
  rw [smoothSpaceTime_split_fderiv hu a hz ht, hinv,
    scalar_fderiv_realTangentCoords (smoothSpaceTime_slice hu ht) a] at hc
  apply hc.congr_of_eventuallyEq
  have hbase : ContinuousAt (fun s => (γ s).proj) θ :=
    ((FiberBundle.continuous_proj (ComplexVector n)
      (TangentSpace 𝓘(ℝ, ComplexVector n))).comp
        (L12Aux.realGeodesicFlow_contMDiff g p).continuous).continuousAt
  filter_upwards [hbase.preimage_mem_nhds (extChartAt_source_mem_nhds
    (I := ComplexModel n) a)] with s hs
  exact congrArg (fun x => u x (T s)) ((extChartAt (ComplexModel n) a).left_inv hs).symm

/-- The one-variable completion of the square with the physical
gradient normalization. -/
theorem harnack_path_derivative_nonneg {P D δ τ ft df N : ℝ}
    (hP : 0 ≤ P) (hδ : 0 < δ)
    (hLY : P / 2 - ft ≤ N / τ) (hdf : -(Real.sqrt P * D) ≤ df) :
    0 ≤ df + δ * ft + N * δ / τ + D ^ 2 / (2 * δ) := by
  have hyoung : Real.sqrt P * D ≤ δ * P / 2 + D ^ 2 / (2 * δ) := by
    apply (mul_le_mul_iff_right₀ hδ).mp
    have hs := sq_nonneg (δ * Real.sqrt P - D)
    have hsq := Real.sq_sqrt hP
    field_simp
    nlinarith
  have h := mul_le_mul_of_nonneg_left hLY hδ.le
  calc
    0 ≤ df + δ * ft + δ * (N / τ) + D ^ 2 / (2 * δ) := by linarith
    _ = _ := by ring

/-- The original differential estimate gives a nonnegative derivative
of the logarithmic Harnack expression along the actual geodesic. -/
theorem positiveHeatSolution_harnack_path_hasDerivAt
    (hLY : LeafCandidates.LiYauDifferential) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)
    {s t θ : ℝ} (hst : s < t) (hτ : 0 < s + (t - s) * θ) :
    letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
      fun z => L12Aux.underlyingRealTangentNormedAddCommGroup g.form z
    ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt
      (fun r => Real.log (u (L12Aux.realGeodesicFlow g p r).proj (s + (t - s) * r)) +
        (n : ℝ) * Real.log (s + (t - s) * r) + ‖p.2‖ ^ 2 * r / (2 * (t - s))) d θ := by
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentNormedAddCommGroup g.form z
  letI : ∀ z : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentInnerProductSpace g.form z
  let τ := s + (t - s) * θ
  let q := L12Aux.realGeodesicFlow g p θ
  let f := fun x => Real.log (u x τ)
  let ft := deriv (fun r => Real.log (u q.proj r)) τ
  let df := mvfderiv 𝓘(ℝ, ComplexVector n) f q.proj q.2
  have hτD : HasDerivAt (fun r : ℝ => s + (t - s) * r) (t - s) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (t - s)).const_add s
  have hf := positiveHeatSolution_log_smoothSpaceTime g.form hu
  have hlog := smoothSpaceTime_geodesic_hasDerivAt g hf p hτD hτ
  have htime := ((hτD.log hτ.ne').const_mul (n : ℝ))
  have hlinear : HasDerivAt (fun r : ℝ => ‖p.2‖ ^ 2 * r / (2 * (t - s)))
      (‖p.2‖ ^ 2 / (2 * (t - s))) θ := by
    simpa using ((hasDerivAt_id θ).const_mul (‖p.2‖ ^ 2)).div_const (2 * (t - s))
  refine ⟨df + (t - s) * ft + (n : ℝ) * (t - s) / τ + ‖p.2‖ ^ 2 / (2 * (t - s)), ?_, ?_⟩
  · apply harnack_path_derivative_nonneg
      (scalarGradientPair_self_nonneg g.form f q.proj) (sub_pos.mpr hst)
    · have hh := hLY n M g hcomplete hK hRic u hu q.proj τ hτ
      have hp := scalarGradientPair_eq_twice_gradNormSq g.form
        (positiveHeatSolution_log_slice g.form hu hτ) q.proj
      change scalarGradientPair g.form f f q.proj = 2 * gradNormSq g.form f q.proj at hp
      change gradNormSq g.form f q.proj - ft ≤ (n : ℝ) / τ at hh
      linarith
    · have hd := scalarDifferential_norm_le_gradient g.form
        (positiveHeatSolution_log_slice g.form hu hτ) q.proj q.2
      rw [L12Aux.realGeodesicFlow_velocity_norm] at hd
      exact (neg_le_neg hd).trans (by simpa only [Real.norm_eq_abs] using neg_abs_le df)
  · convert (hlog.add htime).add hlinear using 1 <;> dsimp only [τ, q, f, ft, df] <;> ring

/-- The logarithmic Harnack inequality for the original arbitrary
positive heat solution, along a genuine minimizing geodesic. -/
theorem positiveHeatSolution_log_harnack
    (hLY : LeafCandidates.LiYauDifferential) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (x y : M.Carrier) :
    Real.log (u x s) ≤ Real.log (u y t) + (n : ℝ) * Real.log (t / s) +
      inducedDistance g.form x y ^ 2 / (2 * (t - s)) := by
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ z : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) z) :=
    fun z => L12Aux.underlyingRealTangentNormedAddCommGroup g.form z
  obtain ⟨v, hv, hnorm⟩ := L12Aux.exists_minimizing_realExponential g x y
  let p : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier := ⟨x, v⟩
  let F : ℝ → ℝ := fun r =>
    Real.log (u (L12Aux.realGeodesicFlow g p r).proj (s + (t - s) * r)) +
      (n : ℝ) * Real.log (s + (t - s) * r) + ‖p.2‖ ^ 2 * r / (2 * (t - s))
  have hD (r : ℝ) (hr : r ∈ Set.Icc (0 : ℝ) 1) :
      ∃ d : ℝ, 0 ≤ d ∧ HasDerivAt F d r := by
    apply positiveHeatSolution_harnack_path_hasDerivAt hLY g hcomplete hK hRic hu p hst
    exact add_pos_of_pos_of_nonneg hs (mul_nonneg (sub_pos.mpr hst).le hr.1)
  have hcont : ContinuousOn F (Set.Icc (0 : ℝ) 1) := by
    intro r hr
    obtain ⟨d, _, hd⟩ := hD r hr
    exact hd.continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ F (interior (Set.Icc (0 : ℝ) 1)) := by
    intro r hr
    obtain ⟨d, _, hd⟩ := hD r (interior_subset hr)
    exact hd.differentiableAt.differentiableWithinAt
  have hmono : MonotoneOn F (Set.Icc (0 : ℝ) 1) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 1) hcont hdiff (by
      intro r hr
      obtain ⟨d, hd, hder⟩ := hD r (interior_subset hr)
      simpa only [hder.deriv] using hd)
  have hh := hmono (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) zero_le_one
  have hbase : (L12Aux.realGeodesicFlow g p 1).proj = y := hv
  have h0 : F 0 = Real.log (u x s) + (n : ℝ) * Real.log s := by
    simp [F, L12Aux.realGeodesicFlow_zero, p]
  have h1 : F 1 = Real.log (u y t) + (n : ℝ) * Real.log t +
      inducedDistance g.form x y ^ 2 / (2 * (t - s)) := by
    simp only [F, mul_one, hbase, show s + (t - s) = t by ring]
    rw [show ‖p.2‖ = inducedDistance g.form x y from hnorm]
  rw [h0, h1] at hh
  rw [Real.log_div (lt_trans hs hst).ne' hs.ne']
  linarith

/-- The precise space-time Harnack inequality in the project's complex
heat normalization. -/
theorem positiveHeatSolution_harnack
    (hLY : LeafCandidates.LiYauDifferential) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (x y : M.Carrier) :
    u x s ≤ (t / s) ^ n * Real.exp (inducedDistance g.form x y ^ 2 / (2 * (t - s))) *
      u y t := by
  have hh := Real.exp_le_exp.mpr
    (positiveHeatSolution_log_harnack hLY g hcomplete hK hRic hu hs hst x y)
  rw [Real.exp_log (hu.2 x s hs).1, Real.exp_add, Real.exp_add,
    Real.exp_log (hu.2 y t (lt_trans hs hst)).1, Real.exp_nat_mul,
    Real.exp_log (div_pos (lt_trans hs hst) hs)] at hh
  nlinarith only [hh]

/-- All positive times in the original definition force arbitrarily
small Gaussian growth on every finite time interval.  The factor near
zero is explicit and will be removed inside weighted trace estimates. -/
theorem positiveHeatSolution_gaussian_growth
    (hLY : LeafCandidates.LiYauDifferential) (g : SmoothMetric M)
    (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    {u : M.Carrier → ℝ → ℝ} (hu : LeafCandidates.PositiveHeatSolution g.form u)
    (o : M.Carrier) {T a : ℝ} (hT : 0 < T) (ha : 0 < a) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → t ≤ T → ∀ x : M.Carrier,
      u x t ≤ C / t ^ n * Real.exp ((a / 2) * inducedDistance g.form o x ^ 2) := by
  let S := T + 1 / a
  have hS : 0 < S := add_pos hT (one_div_pos.mpr ha)
  refine ⟨S ^ n * u o S, mul_pos (pow_pos hS _) (hu.2 o S hS).1, ?_⟩
  intro t ht htT x
  have htS : t < S := lt_of_le_of_lt htT (lt_add_of_pos_right T (one_div_pos.mpr ha))
  have hδ : 0 < S - t := sub_pos.mpr htS
  have hδa : 1 ≤ (S - t) * a := by
    apply (div_le_iff₀ ha).mp
    dsimp [S]
    linarith
  have hExp : inducedDistance g.form o x ^ 2 / (2 * (S - t)) ≤
      (a / 2) * inducedDistance g.form o x ^ 2 := by
    apply (div_le_iff₀ (mul_pos (by norm_num) hδ)).mpr
    have hh := mul_le_mul_of_nonneg_right hδa (sq_nonneg (inducedDistance g.form o x))
    nlinarith only [hh]
  have hh := positiveHeatSolution_harnack hLY g hcomplete hK hRic hu ht htS x o
  rw [g.induced_distance_symm x o] at hh
  calc
    u x t ≤ (S / t) ^ n * Real.exp (inducedDistance g.form o x ^ 2 / (2 * (S - t))) * u o S := hh
    _ ≤ (S / t) ^ n * Real.exp ((a / 2) * inducedDistance g.form o x ^ 2) * u o S :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hExp)
        (pow_nonneg (div_nonneg hS.le ht.le) _)) (hu.2 o S hS).1.le
    _ = _ := by rw [div_pow]; ring

end Yau.LeafProofs.L19Aux
