import Yau.LeafProofs.L23FieldMetric

/-! MetricSmooth coordinate formulas for the genuine real Levi-Civita connection. -/
noncomputable section
open MeasureTheory Filter Bundle
open scoped Topology Manifold ENNReal Matrix ContDiff
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem realCoordinateMetric_mdifferentiableAt (h : HermitianField M) (hh : MetricSmooth h) (x y : M.Carrier)
    (u v : ComplexVector n) (hy : y ∈ (chartAt (ComplexVector n) x).source) :
    MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (realCoordinateMetric h x u v) y := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle h
  letI := realRiemannianBundle_contMDiff h hh
  have hs := (realCoordinateField_contMDiffAt x y u hy).inner_bundle
    (realCoordinateField_contMDiffAt x y v hy)
  convert! hs.mdifferentiableAt (by simp) using 1

theorem mvfderiv_realCoordinateMetric (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    mvfderiv 𝓘(ℝ, ComplexVector n)
      (realCoordinateMetric h x (realVec b) (realVec c)) (chartInv x z)
      (realCoordinateField x (realVec a) (chartInv x z)) =
        rDeriv (fun w => realMetricFn h x w b c) z a := by
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  rw [mvfderiv_realCoordinateField _ x z (realVec a) hz
    (realCoordinateMetric_mdifferentiableAt h hh x (chartInv x z) _ _ hy)]
  have heq : (fun w => realCoordinateMetric h x (realVec b) (realVec c) (chartInv x w))
      =ᶠ[𝓝 z] (fun w => realMetricFn h x w b c) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    exact realCoordinateMetric_inChart h x w hw b c
  unfold rDeriv
  rw [heq.fderiv_eq]

theorem realLeviCivitaConnection_frame_inner (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    letI := manifold_realSmooth M
    (underlyingRealRiemannianMetric h).inner (chartInv x z)
      (realLeviCivitaConnection h hh (realCoordinateField x (realVec b)) (chartInv x z)
        (realCoordinateField x (realVec a) (chartInv x z)))
      (realCoordinateField x (realVec c) (chartInv x z)) =
        (rDeriv (fun w => realMetricFn h x w b c) z a +
          rDeriv (fun w => realMetricFn h x w c a) z b -
          rDeriv (fun w => realMetricFn h x w a b) z c) / 2 := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle h
  letI := realRiemannianBundle_contMDiff h hh
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have hA := (realCoordinateField_contMDiffAt x (chartInv x z) (realVec a) hy).mdifferentiableAt (by simp)
  have hB := (realCoordinateField_contMDiffAt x (chartInv x z) (realVec b) hy).mdifferentiableAt (by simp)
  have hC := (realCoordinateField_contMDiffAt x (chartInv x z) (realVec c) hy).mdifferentiableAt (by simp)
  have hk := CovariantDerivative.leviCivitaConnection_apply_inner
    𝓘(ℝ, ComplexVector n) hA hB hC
  simp only [realCoordinateField_mlieBracket x (chartInv x z) _ _ hy,
    inner_zero_right, sub_zero, add_zero] at hk
  change (underlyingRealRiemannianMetric h).inner (chartInv x z)
      (realLeviCivitaConnection h hh (realCoordinateField x (realVec b)) (chartInv x z)
        (realCoordinateField x (realVec a) (chartInv x z)))
      (realCoordinateField x (realVec c) (chartInv x z)) =
        (mvfderiv 𝓘(ℝ, ComplexVector n)
          (realCoordinateMetric h x (realVec b) (realVec c)) (chartInv x z)
          (realCoordinateField x (realVec a) (chartInv x z)) +
         mvfderiv 𝓘(ℝ, ComplexVector n)
          (realCoordinateMetric h x (realVec c) (realVec a)) (chartInv x z)
          (realCoordinateField x (realVec b) (chartInv x z)) -
         mvfderiv 𝓘(ℝ, ComplexVector n)
          (realCoordinateMetric h x (realVec a) (realVec b)) (chartInv x z)
          (realCoordinateField x (realVec c) (chartInv x z))) / 2 at hk
  rw [mvfderiv_realCoordinateMetric h hh x z hz a b c,
    mvfderiv_realCoordinateMetric h hh x z hz b c a,
    mvfderiv_realCoordinateMetric h hh x z hz c a b] at hk
  exact hk



theorem christoffel_metric_contraction (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b c : RIdx n) :
    (∑ d, christoffel h x z d a b * realMetricFn h x z d c) =
      (rDeriv (fun w => realMetricFn h x w b c) z a +
        rDeriv (fun w => realMetricFn h x w a c) z b -
        rDeriv (fun w => realMetricFn h x w a b) z c) / 2 := by
  let G := realMetricFn h x z
  let D : RIdx n → ℝ := fun d => rDeriv (fun w => realMetricFn h x w b d) z a +
    rDeriv (fun w => realMetricFn h x w a d) z b -
    rDeriv (fun w => realMetricFn h x w a b) z d
  have hv : G *ᵥ (G⁻¹ *ᵥ D) = D := by
    rw [Matrix.mulVec_mulVec,
      Matrix.mul_nonsing_inv G (isUnit_iff_ne_zero.mpr (realMetricFn_posDef h x z hz).det_pos.ne'),
      Matrix.one_mulVec]
  calc
    _ = (1 / 2 : ℝ) * (G *ᵥ (G⁻¹ *ᵥ D)) c := by
      unfold christoffel
      change (∑ d, ((1 / 2 : ℝ) * ∑ e, G⁻¹ d e * D e) * G d c) = _
      simp only [Matrix.mulVec, dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro d _
      rw [show G d c = G c d from realMetricFn_symm h x z d c]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e _
      ring
    _ = _ := by rw [hv]; dsimp [D]; ring


theorem realLeviCivitaConnection_frame (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a b : RIdx n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection h hh (realCoordinateField x (realVec b)) (chartInv x z)
      (realCoordinateField x (realVec a) (chartInv x z)) =
        ∑ d, christoffel h x z d a b • realCoordinateField x (realVec d) (chartInv x z) := by
  letI := manifold_realSmooth M
  letI := realRiemannianBundle h
  letI := realRiemannianBundle_contMDiff h hh
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have htest (c : RIdx n) :
      (underlyingRealRiemannianMetric h).inner (chartInv x z)
        (realLeviCivitaConnection h hh (realCoordinateField x (realVec b)) (chartInv x z)
          (realCoordinateField x (realVec a) (chartInv x z)))
        (realCoordinateField x (realVec c) (chartInv x z)) =
      (underlyingRealRiemannianMetric h).inner (chartInv x z)
        (∑ d, christoffel h x z d a b • realCoordinateField x (realVec d) (chartInv x z))
        (realCoordinateField x (realVec c) (chartInv x z)) := by
    rw [realLeviCivitaConnection_frame_inner h hh x z hz a b c,
      map_sum ((underlyingRealRiemannianMetric h).inner (chartInv x z)),
      ContinuousLinearMap.sum_apply]
    simp only [map_smul, ContinuousLinearMap.smul_apply, smul_eq_mul]
    have hinner (d : RIdx n) :
        (underlyingRealRiemannianMetric h).inner (chartInv x z)
          (realCoordinateField x (realVec d) (chartInv x z))
          (realCoordinateField x (realVec c) (chartInv x z)) =
        realMetricFn h x z d c := realCoordinateMetric_inChart h x z hz d c
    simp_rw [hinner]
    rw [christoffel_metric_contraction h hh x z hz a b c]
    rw [show (fun w => realMetricFn h x w c a) =
      (fun w => realMetricFn h x w a c) from
        funext fun w => realMetricFn_symm h x w c a]
  apply ext_inner_right ℝ
  intro w
  obtain ⟨r, hr⟩ := realCoordinateField_span x (chartInv x z) hy w
  rw [hr, inner_sum, inner_sum]
  apply Finset.sum_congr rfl
  intro c _
  simp only [inner_smul_right, RCLike.conj_to_real]
  exact congrArg (fun t : ℝ => r c * t) (htest c)


theorem realLeviCivitaConnection_finset_sum {ι : Type*} (h : HermitianField M) (hh : MetricSmooth h) (s : Finset ι)
    (W : ι → ∀ y : M.Carrier, TangentSpace 𝓘(ℝ, ComplexVector n) y)
    (p : M.Carrier) (v : TangentSpace 𝓘(ℝ, ComplexVector n) p)
    (hW : letI := manifold_realSmooth M
      ∀ i ∈ s, MDifferentiableAt 𝓘(ℝ, ComplexVector n)
        (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
          (fun y => (⟨y, W i y⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) p) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection h hh (∑ i ∈ s, W i) p v =
      ∑ i ∈ s, realLeviCivitaConnection h hh (W i) p v := by
  classical
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection h hh
  change cov (∑ i ∈ s, W i) p v = ∑ i ∈ s, cov (W i) p v
  induction s using Finset.induction_on with
  | empty => simp [cov.zero]
  | @insert i s hi ih =>
    rw [Finset.forall_mem_insert] at hW
    have hs := MDifferentiableAt.sum_section hW.2
    have hadd : cov (W i + ∑ j ∈ s, W j) p = cov (W i) p + cov (∑ j ∈ s, W j) p := by
      apply cov.isCovariantDerivativeOnUniv.add hW.1
      convert! hs using 1
      simp only [Finset.sum_apply]
    simp only [Finset.sum_insert hi]
    rw [hadd, ContinuousLinearMap.add_apply, ih hW.2]

def realConnectionFrame (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) (a b : RIdx n) :
    ∀ y : M.Carrier, TangentSpace 𝓘(ℝ, ComplexVector n) y := by
  letI := manifold_realSmooth M
  exact fun y => realLeviCivitaConnection h hh (realCoordinateField x (realVec b)) y
    (realCoordinateField x (realVec a) y)

theorem realConnectionFrame_eq_sum (h : HermitianField M) (hh : MetricSmooth h) (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) (a b : RIdx n) :
    realConnectionFrame h hh x a b y =
      ∑ d, christoffel h x (chartPt x y) d a b • realCoordinateField x (realVec d) y := by
  have hz : chartPt x y ∈ chartTarget x :=
    (extChartAt (ComplexModel n) x).map_source (by simpa only [extChartAt_source] using hy)
  have hi : chartInv x (chartPt x y) = y :=
    (extChartAt (ComplexModel n) x).left_inv (by simpa only [extChartAt_source] using hy)
  have hk := realLeviCivitaConnection_frame h hh x (chartPt x y) hz a b
  rw [hi] at hk
  exact hk


theorem realLeviCivitaConnection_frame_sum (h : HermitianField M) (hh : MetricSmooth h) (x y : M.Carrier)
    (hy : y ∈ (chartAt (ComplexVector n) x).source) (a : RIdx n)
    (C : RIdx n → M.Carrier → ℝ)
    (hC : ∀ d, MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (C d) y) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection h hh (∑ d, fun p => C d p • realCoordinateField x (realVec d) p) y
      (realCoordinateField x (realVec a) y) =
    ∑ d, (C d y • (∑ e, christoffel h x (chartPt x y) e a d •
      realCoordinateField x (realVec e) y) +
      mvfderiv 𝓘(ℝ, ComplexVector n) (C d) y (realCoordinateField x (realVec a) y) •
        realCoordinateField x (realVec d) y) := by
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection h hh
  have hD (d : RIdx n) :=
    (realCoordinateField_contMDiffAt x y (realVec d) hy).mdifferentiableAt (by simp)
  change cov (∑ d, C d • realCoordinateField x (realVec d)) y
    (realCoordinateField x (realVec a) y) = _
  rw [realLeviCivitaConnection_finset_sum h hh Finset.univ _ y _
    (fun d _ => (hC d).smul_section (hD d))]
  apply Finset.sum_congr rfl
  intro d _
  have hleib := cov.isCovariantDerivativeOnUniv.leibniz (hD d) (hC d)
  change cov ((C d) • realCoordinateField x (realVec d)) y _ = _
  rw [hleib]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smulRight_apply]
  have he := realConnectionFrame_eq_sum h hh x y hy a d
  change cov (realCoordinateField x (realVec d)) y
    (realCoordinateField x (realVec a) y) = _ at he
  rw [he]


theorem metricDirectionalDerivative_eq_connection (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (a : RIdx n) :
    matrixDirectionalDerivative (fun w => realMetricFn h x w) z (realVec a) =
      (connectionMatrix h x z a)ᵀ * realMetricFn h x z +
        realMetricFn h x z * connectionMatrix h x z a := by
  ext b c
  change rDeriv (fun w => realMetricFn h x w b c) z a = _
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix]
  have hswap : (∑ d, realMetricFn h x z b d * christoffel h x z d a c) =
      ∑ d, christoffel h x z d a c * realMetricFn h x z d b := by
    apply Finset.sum_congr rfl
    intro d _
    rw [realMetricFn_symm h x z b d]
    ring
  rw [hswap, christoffel_metric_contraction h hh x z hz a b c,
    christoffel_metric_contraction h hh x z hz a c b,
    rDeriv_realMetricFn_symm h x z a c b]
  ring

set_option synthInstance.maxHeartbeats 200000 in
theorem realMetricInChart_connection_compatibility (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (w u v : ComplexVector n) :
    (fderiv ℝ (realMetricInChart h x) z w) u v =
      realMetricInChart h x z (chartChristoffelBilin h x z w u) v +
        realMetricInChart h x z u (chartChristoffelBilin h x z w v) := by
  have hB := ((realMetricInChart_smooth h hh x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)
  apply metricCompatibility_of_basis (realVec_basis n) (realMetricInChart h x z)
    (chartChristoffelBilin h x z) (fderiv ℝ (realMetricInChart h x) z) _ w u v
  intro a b c
  simp only [realVec_basis_apply]
  rw [← fderiv_bilin_apply_const hB (realVec a) (realVec b) (realVec c)]
  have he : (fun t => realMetricInChart h x t (realVec b) (realVec c)) =ᶠ[𝓝 z]
      (fun t => realMetricFn h x t b c) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with t ht
    exact realMetricInChart_basis h x t ht b c
  rw [he.fderiv_eq, chartChristoffelBilin_basis, chartChristoffelBilin_basis]
  rw [map_sum, sum_apply, map_sum]
  simp only [map_smul, smul_apply, smul_eq_mul, realMetricInChart_basis h x z hz]
  have hh := congrFun (congrFun (metricDirectionalDerivative_eq_connection h hh x z hz a) b) c
  change rDeriv (fun t => realMetricFn h x t b c) z a = _ at hh
  simp only [Matrix.add_apply, Matrix.mul_apply, Matrix.transpose_apply, connectionMatrix] at hh
  simpa only [rDeriv, mul_comm] using hh


theorem realLeviCivitaConnection_coordinateVectorField_basis (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (V : ComplexVector n → ComplexVector n) (hV : ContDiffAt ℝ ∞ V z) (a : RIdx n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection h hh (realCoordinateVectorField x V) (chartInv x z)
      (realCoordinateField x (realVec a) (chartInv x z)) =
      realFrameCLM x (chartInv x z)
        (fderiv ℝ V z (realVec a) + chartChristoffelBilin h x z (realVec a) (V z)) := by
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection h hh
  let y := chartInv x z
  have hy : y ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv, y] using (extChartAt (ComplexModel n) x).map_target hz
  have hpt : chartPt x y = z := (extChartAt (ComplexModel n) x).right_inv hz
  let F : RIdx n → ComplexVector n → ℝ := fun d w => realCoord (V w) d
  let C : RIdx n → M.Carrier → ℝ := fun d p => F d (chartPt x p)
  have hF (d) : ContDiffAt ℝ ∞ (F d) z :=
    (contDiff_realCoord d).contDiffAt.comp z hV
  have hC (d) : MDifferentiableAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ℝ) (C d) y := by
    apply (contMDiffAt_chartLift_of_contDiffAt x y hy _).mdifferentiableAt (by simp)
    simpa only [hpt] using hF d
  have hW : MDifferentiableAt 𝓘(ℝ, ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (fun p => (⟨p, realCoordinateVectorField x V p⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) y := by
    apply (realCoordinateVectorField_contMDiffAt x y hy V _).mdifferentiableAt (by simp)
    simpa only [hpt] using hV
  let W := ∑ d, C d • realCoordinateField x (realVec d)
  have hWs : MDifferentiableAt 𝓘(ℝ, ComplexVector n)
      (𝓘(ℝ, ComplexVector n).prod 𝓘(ℝ, ComplexVector n))
      (fun p => (⟨p, W p⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) y := by
    convert! MDifferentiableAt.sum_section (s := Finset.univ) (fun d _ =>
      (hC d).smul_section ((realCoordinateField_contMDiffAt x y (realVec d) hy).mdifferentiableAt (by simp))) using 1
    simp only [W, Finset.sum_apply, Pi.smul_apply]
  have heq : realCoordinateVectorField x V =ᶠ[𝓝 y] W := by
    filter_upwards [(chartAt (ComplexVector n) x).open_source.mem_nhds hy] with p hp
    rw [realCoordinateVectorField_eq_sum x p hp V]
    simp only [W, Finset.sum_apply]
    apply Finset.sum_congr rfl
    intro d _
    rfl
  have hloc := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hW hWs Filter.univ_mem heq
  change cov (realCoordinateVectorField x V) y _ = _
  rw [hloc]
  have hsum := realLeviCivitaConnection_frame_sum h hh x y hy a C hC
  change cov W y (realCoordinateField x (realVec a) y) = _ at hsum
  rw [hsum]
  have hd (d) : mvfderiv 𝓘(ℝ, ComplexVector n) (C d) y
      (realCoordinateField x (realVec a) y) = realCoord (fderiv ℝ V z (realVec a)) d := by
    rw [mvfderiv_chartLift_of_contDiffAt x z (realVec a) hz (hF d)]
    exact realCoord_fderiv_comp (hV.differentiableAt (by simp)) (realVec a) d
  have hΓ : chartChristoffelBilin h x z (realVec a) (V z) =
      ∑ d, realCoord (V z) d • (∑ e, christoffel h x z e a d • realVec e) := by
    conv_lhs => rw [← sum_realCoord_realVec (V z)]
    rw [map_sum]
    simp only [map_smul, chartChristoffelBilin_basis]
  simp only [C, F, hpt, hd]
  conv_rhs => rw [map_add, ← sum_realCoord_realVec (fderiv ℝ V z (realVec a)), hΓ]
  simp only [map_sum, map_smul]
  simp only [realFrameCLM_apply x (chartInv x z) hy]
  rw [Finset.sum_add_distrib, add_comm]

theorem realLeviCivitaConnection_coordinateVectorField (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (V : ComplexVector n → ComplexVector n) (hV : ContDiffAt ℝ ∞ V z) (u : ComplexVector n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection h hh (realCoordinateVectorField x V) (chartInv x z)
      (realCoordinateField x u (chartInv x z)) =
      realFrameCLM x (chartInv x z) (fderiv ℝ V z u + chartChristoffelBilin h x z u (V z)) := by
  letI := manifold_realSmooth M
  let y := chartInv x z
  have hy : y ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv, y] using (extChartAt (ComplexModel n) x).map_target hz
  let cov := realLeviCivitaConnection h hh
  let A := (cov (realCoordinateVectorField x V) y).comp (realFrameCLM x y)
  let B := (realFrameCLM x y).comp (fderiv ℝ V z + (chartChristoffelBilin h x z).flip (V z))
  have hAB : A.toLinearMap = B.toLinearMap := by
    apply (realVec_basis n).ext
    intro a
    change cov (realCoordinateVectorField x V) y (realFrameCLM x y (realVec_basis n a)) =
      realFrameCLM x y (fderiv ℝ V z (realVec_basis n a) + chartChristoffelBilin h x z (realVec_basis n a) (V z))
    rw [realVec_basis_apply, realFrameCLM_apply x y hy]
    exact realLeviCivitaConnection_coordinateVectorField_basis h hh x z hz V hV a
  have he := congrArg (fun L : ComplexVector n →ₗ[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) y => L u) hAB
  change cov (realCoordinateVectorField x V) y (realFrameCLM x y u) =
    realFrameCLM x y (fderiv ℝ V z u + chartChristoffelBilin h x z u (V z)) at he
  rw [realFrameCLM_apply x y hy u] at he
  exact he

theorem realLeviCivitaConnection_coordinateVectorField_realChartVec (h : HermitianField M) (hh : MetricSmooth h)
    (x : M.Carrier) (z : ComplexVector n) (hz : z ∈ chartTarget x)
    (V : ComplexVector n → ComplexVector n) (hV : ContDiffAt ℝ ∞ V z) (u : ComplexVector n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection h hh (realCoordinateVectorField x V) (chartInv x z) (realChartVec x z u) =
      realChartVec x z (fderiv ℝ V z u + chartChristoffelBilin h x z u (V z)) := by
  letI := manifold_realSmooth M
  have hy : chartInv x z ∈ (chartAt (ComplexVector n) x).source := by
    simpa only [extChartAt_source, chartInv] using (extChartAt (ComplexModel n) x).map_target hz
  have he := realLeviCivitaConnection_coordinateVectorField h hh x z hz V hV u
  rw [realFrameCLM_apply x (chartInv x z) hy,
    realCoordinateField_eq_realChartVec x z u hz,
    realCoordinateField_eq_realChartVec x z _ hz] at he
  exact he


theorem realLeviCivitaConnection_constFrame (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (u v : ComplexVector n) :
    letI := manifold_realSmooth M
    realLeviCivitaConnection h hh (realCoordinateField x v) (chartInv x z)
      (realCoordinateField x u (chartInv x z)) =
      realFrameCLM x (chartInv x z) (chartChristoffelBilin h x z u v) := by
  letI := manifold_realSmooth M
  have he := realLeviCivitaConnection_coordinateVectorField h hh x z hz (fun _ => v) contDiffAt_const u
  change realLeviCivitaConnection h hh (realCoordinateField x v) (chartInv x z)
    (realCoordinateField x u (chartInv x z)) = realFrameCLM x (chartInv x z)
      (fderiv ℝ (fun _ : ComplexVector n => v) z u + chartChristoffelBilin h x z u v) at he
  simpa only [fderiv_const_apply, ContinuousLinearMap.zero_apply, zero_add] using he


set_option maxHeartbeats 800000 in
theorem chartChristoffelBilin_change (h : HermitianField M) (hh : MetricSmooth h) (a b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hy : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) (u w : ComplexVector n) :
    fderiv ℝ (realChartChange a b) z (chartChristoffelBilin h a z u w) =
      fderiv ℝ (fderiv ℝ (realChartChange a b)) z u w +
        chartChristoffelBilin h b (realChartChange a b z)
          (fderiv ℝ (realChartChange a b) z u) (fderiv ℝ (realChartChange a b) z w) := by
  letI := manifold_realSmooth M
  let cov := realLeviCivitaConnection h hh
  let p := chartInv a z
  let zB := realChartChange a b z
  have hA : p ∈ (extChartAt (ComplexModel n) a).source := (extChartAt (ComplexModel n) a).map_target hz
  have hAr : p ∈ (chartAt (ComplexVector n) a).source := by simpa only [extChartAt_source] using hA
  have hBr : p ∈ (chartAt (ComplexVector n) b).source := by simpa only [extChartAt_source] using hy
  have hzB : zB ∈ chartTarget b := (extChartAt (ComplexModel n) b).map_source hy
  have hbInv : chartInv b zB = p := (extChartAt (ComplexModel n) b).left_inv hy
  have hV := realChartChange_pushVector_contDiffAt a b hz hy w
  have hWA := (realCoordinateField_contMDiffAt a p w hAr).mdifferentiableAt (by simp)
  have hWB := (realCoordinateVectorField_contMDiffAt b p hBr
    (realChartChange_pushVector a b w) hV).mdifferentiableAt (by simp)
  have hloc := cov.isCovariantDerivativeOnUniv.congr_of_eventuallyEq hWA hWB Filter.univ_mem
    (realCoordinateField_eq_pushVector_eventually a b hz hy w)
  have hAconn := realLeviCivitaConnection_constFrame h hh a z hz u w
  have hBconn := realLeviCivitaConnection_coordinateVectorField h hh b zB hzB
    (realChartChange_pushVector a b w) hV (fderiv ℝ (realChartChange a b) z u)
  rw [hbInv] at hBconn
  have hVp : realChartChange_pushVector a b w zB = fderiv ℝ (realChartChange a b) z w := by
    unfold realChartChange_pushVector
    rw [realChartChange_inverse_apply a b hz hy]
  rw [realChartChange_pushVector_fderiv a b hz hy u w, hVp] at hBconn
  have hU : realCoordinateField a u p =
      realCoordinateField b (fderiv ℝ (realChartChange a b) z u) p := by
    have hh := realChartChange_frame a b hz hy u
    rw [realFrameCLM_apply b (chartInv a z) hBr] at hh
    exact hh.symm
  have hconn : realFrameCLM a p (chartChristoffelBilin h a z u w) =
      realFrameCLM b p (fderiv ℝ (fderiv ℝ (realChartChange a b)) z u w +
        chartChristoffelBilin h b zB
          (fderiv ℝ (realChartChange a b) z u) (fderiv ℝ (realChartChange a b) z w)) := by
    rw [← hAconn, hloc, hU]
    exact hBconn
  have he := congrArg (realTangentCoords b p) hconn
  rw [realFrameCLM_apply a p hAr, realTangentCoords_realFrameCLM b p hBr,
    ← realChartChange_fderiv a b hz hy (chartChristoffelBilin h a z u w)] at he
  exact he


end Yau.LeafProofs.L23Aux
