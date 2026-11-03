import Yau.LeafProofs.L23FieldMetricNormalInverse

/-! The regularized inverse-normal radius satisfies the actual path-length bound. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 600000

theorem chartVectorNorm_curve_coordinates (h : HermitianField M)
    (c : M.Carrier) (β : ℝ → M.Carrier) (t : ℝ)
    (hy : β t ∈ (chartAt (ComplexVector n) c).source) :
    letI := manifold_realSmooth M
    letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
      fun y => underlyingRealTangentNormedAddCommGroup h y
    MDifferentiableAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) β t →
    ∀ (v : ComplexVector n), HasDerivAt (fun s => chartPt c (β s)) v t →
      chartVectorNorm h c (chartPt c (β t)) v = ‖realCurveVelocity β t‖ := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  intro hβ v hv
  have H := realCurveVelocity_coords_of_hasDerivAt β t c v hy hβ hv
  unfold chartVectorNorm
  rw [← H,realMetricInChart_tangentCoords h c (β t) hy]
  change Real.sqrt (inner ℝ (realCurveVelocity β t) (realCurveVelocity β t)) = ‖realCurveVelocity β t‖
  rw [real_inner_self_eq_norm_sq,Real.sqrt_sq (norm_nonneg _)]

theorem normalEndpoint_inverse_radius_sub_le_pathELength
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (B : Set (ComplexVector n)) (hB : IsOpen B) {ρ ε d : ℝ} (hε : 0 < ε) (hd : 0 < d)
    (η : (ComplexVector n × ComplexVector n) → ℝ → ComplexVector n × ComplexVector n)
    (e : OpenPartialHomeomorph (ComplexVector n × ComplexVector n) (ComplexVector n × ComplexVector n))
    (hsource : e.source = B ×ˢ Metric.ball (0 : ComplexVector n) ρ)
    (he : Set.EqOn e (fun p => (p.1,(η p 1).1)) e.source)
    (hinv : ContDiffOn ℝ 3 e.symm e.target)
    (hη : ContDiffOn ℝ 2 (Function.uncurry η)
      ((B ×ˢ Metric.ball (0 : ComplexVector n) ρ) ×ˢ Set.Ioo (-ε) (1+ε)))
    (hi : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ, η p 0 = p)
    (hs : ∀ p ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ,
      ∀ u ∈ Set.Ioo (-ε) (1+ε), (η p u).1 ∈ chartTarget c ∧
        HasDerivAt (η p) (chartGeodesicSpray h c (η p u)) u)
    (z : ComplexVector n) (β : ℝ → M.Carrier) (a b : ℝ) (hab : a ≤ b) :
    letI := manifold_realSmooth M
    ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 β →
    (∀ u ∈ Set.Icc a b, β u ∈ (chartAt (ComplexVector n) c).source ∧
      (z,chartPt c (β u)) ∈ e.target) →
    ENNReal.ofReal (regularizedChartRadius h c z d (e.symm (z,chartPt c (β b))).2-
      regularizedChartRadius h c z d (e.symm (z,chartPt c (β a))).2) ≤
        fieldPathELength h β a b := by
  letI := manifold_realSmooth M
  letI : ∀ y : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentNormedAddCommGroup h y
  letI : ∀ y : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) y) :=
    fun y => underlyingRealTangentInnerProductSpace h y
  intro hβ htarget
  let H : ℝ → ℝ := fun u => regularizedChartRadius h c z d (e.symm (z,chartPt c (β u))).2
  have hcoord (u : ℝ) (hu : u ∈ Set.Icc a b) :
      ContDiffAt ℝ 1 (fun s => chartPt c (β s)) u := by
    have Hchart : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1 (chartPt c) (β u) := by
      convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n))
        (x := c) (x' := β u) (htarget u hu).1) using 1
      infer_instance
    exact (Hchart.comp u hβ.contMDiffAt).contDiffAt
  have hHC : ContDiffOn ℝ 1 H (Set.Icc a b) := by
    intro u hu
    have hPair : ContDiffAt ℝ 1 (fun s => (z,chartPt c (β s))) u := contDiffAt_const.prodMk (hcoord u hu)
    have hInv : ContDiffAt ℝ 1 e.symm (z,chartPt c (β u)) :=
      (hinv.contDiffAt (e.open_target.mem_nhds (htarget u hu).2)).of_le (by norm_num)
    have hLog : ContDiffAt ℝ 1 (fun s => (e.symm (z,chartPt c (β s))).2) u :=
      (hInv.comp u hPair).snd
    exact (((regularizedChartRadius_contDiff h c z hd).of_le (by simp)).contDiffAt.comp u hLog).contDiffWithinAt
  have hFTC := enorm_sub_le_lintegral_deriv_of_contDiffOn_Icc hHC hab
  have hbound : (∫⁻ u in Set.Icc a b, ‖deriv H u‖ₑ) ≤ fieldPathELength h β a b := by
    change _ ≤ Manifold.pathELength 𝓘(ℝ, ComplexVector n) β a b
    rw [Manifold.pathELength_eq_lintegral_mfderiv_Icc]
    apply setLIntegral_mono' measurableSet_Icc
    intro u hu
    have hβcoord := ((hcoord u hu).differentiableAt (by norm_num)).hasDerivAt
    obtain ⟨HD,HB⟩ := normalEndpoint_inverse_radius_hasDerivAt h hh c B hB hε hd η e
      hsource he hinv hη hi hs z hβcoord (htarget u hu).2
    rw [chartVectorNorm_curve_coordinates h c β u (htarget u hu).1
      (hβ.contMDiffAt.mdifferentiableAt (by norm_num)) _ hβcoord] at HB
    rw [← HD.deriv] at HB
    change ‖deriv H u‖ₑ ≤ ‖realCurveVelocity β u‖ₑ
    simpa only [← ofReal_norm,Real.norm_eq_abs,H] using ENNReal.ofReal_le_ofReal HB
  exact (ENNReal.ofReal_le_ofReal (le_abs_self _)).trans
    (by simpa only [← ofReal_norm,Real.norm_eq_abs,H] using hFTC.trans hbound)

end Yau.LeafProofs.L23Aux
