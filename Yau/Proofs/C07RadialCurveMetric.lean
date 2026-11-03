import Yau.Proofs.C07PullbackBounds

open scoped Manifold Topology ContDiff Matrix ComplexOrder

noncomputable section

namespace Yau.Proofs.C07RadialCurveAux

open Yau Yau.Blueprint Set Filter
open Yau.Blueprint.Alignment.Y03Proof

variable {n : ℕ} {M : ComplexManifold n}

theorem chart_quadratic_norm (k : HermitianField M) (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) (v : ComplexVector n) :
    (star (WithLp.ofLp v) ⬝ᵥ (hMat k a (chartPt a y) *ᵥ WithLp.ofLp v)).re =
      hermitianNormSq (k y) (chartVec a y v) := by
  have hsum : ∀ q : ComplexVector n,
      (∑ i, v i • chartVec a (chartInv a q) (stdVec i)) = chartVec a (chartInv a q) v := by
    intro q
    let L : ComplexVector n →L[ℂ] TangentVector M (chartInv a q) :=
      (mfderiv (ComplexModel n) (ComplexModel n) (extChartAt (ComplexModel n) a).symm
        (chartPt a (chartInv a q))).comp
        (NormedSpace.fromTangentSpace (𝕜 := ℂ) (chartPt a (chartInv a q))).symm.toContinuousLinearMap
    change (∑ i, v i • L (stdVec i)) = L v
    conv_rhs => rw [← sum_stdVec v]
    simp only [map_sum, map_smul]
  rw [hMat_quadratic, hsum]
  exact congrArg (fun y => hermitianNormSq (k y) (chartVec a y v))
    ((extChartAt (ComplexModel n) a).left_inv hy)

theorem chartVec_tangentCoords (a y : M.Carrier)
    (hy : y ∈ (extChartAt (ComplexModel n) a).source) (v : TangentVector M y) :
    chartVec a y (tangentCoords a y v) = v := by
  have h := mfderivWithin_extChartAt_symm_comp_mfderiv_extChartAt'
    (I := ComplexModel n) hy
  rw [ModelWithCorners.range_eq_univ, mfderivWithin_univ] at h
  exact congrArg (fun L => L v) h

/-- Matrix order in the actual centre chart is order on all intrinsic
tangent vectors. -/
theorem hermitianNormSq_mono {k₁ k₀ : HermitianField M}
    (horder : ∀ y, HermLE (gMat k₁ y) (gMat k₀ y))
    (y : M.Carrier) (v : TangentVector M y) :
    hermitianNormSq (k₁ y) v ≤ hermitianNormSq (k₀ y) v := by
  let w := tangentCoords y y v
  have hquad (k : HermitianField M) :
      (star (WithLp.ofLp w) ⬝ᵥ (gMat k y *ᵥ WithLp.ofLp w)).re =
        hermitianNormSq (k y) v := by
    rw [gMat, chart_quadratic_norm k y y (mem_extChartAt_source y)]
    exact congrArg (hermitianNormSq (k y))
      (chartVec_tangentCoords y y (mem_extChartAt_source y) v)
  have h := (Complex.nonneg_iff.mp
    ((horder y).dotProduct_mulVec_nonneg (WithLp.ofLp w))).1
  simpa only [Matrix.sub_mulVec, dotProduct_sub, Complex.sub_re,
    hquad, sub_nonneg] using h

theorem hMat_continuousOn (k : HermitianField M) (hk : MetricSmooth k)
    (a : M.Carrier) (i j : Fin n) :
    ContinuousOn (fun q => hMat k a q i j) (chartTarget a) := by
  simp_rw [hMat_of_realMetricFn]
  have h₁ := Complex.ofRealCLM.continuous.comp_continuousOn
    ((hk a (i, 0) (j, 0)).continuousOn.div_const 2)
  have h₂ := Complex.ofRealCLM.continuous.comp_continuousOn
    ((hk a (i, 0) (j, 1)).continuousOn.div_const 2)
  convert h₁.sub ((continuousOn_const (c := Complex.I)).mul h₂) using 1
  funext q
  simp [Complex.ofReal_div]

/-- The norm of the genuine differential of a smooth chart map is
continuous, even though the pointwise tangent representatives use the
chart based at the current image point. -/
theorem pullback_energy_continuousOn (k : HermitianField M) (hk : MetricSmooth k)
    {Φ : ComplexVector n → M.Carrier} {r : ℝ}
    (hΦ : ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Φ (Metric.ball 0 r))
    (v : ComplexVector n) :
    ContinuousOn (fun w => hermitianNormSq (k (Φ w))
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ w v)) (Metric.ball 0 r) := by
  intro w₀ hw₀
  let a := Φ w₀
  let U := Metric.ball (0 : ComplexVector n) r ∩ Φ ⁻¹' (chartAt (ComplexVector n) a).source
  have hU : IsOpen U := hΦ.continuousOn.isOpen_inter_preimage Metric.isOpen_ball
    (chartAt (ComplexVector n) a).open_source
  have hwU : w₀ ∈ U := ⟨hw₀, mem_chart_source (ComplexVector n) a⟩
  let G : ComplexVector n → ComplexVector n := fun w => chartPt a (Φ w)
  have hG : ContDiffOn ℂ ∞ G U :=
    ((contMDiffOn_extChartAt (I := ComplexModel n) (x := a) (n := ∞)).comp
      (hΦ.mono inter_subset_left) (fun _ hw => hw.2)).contDiffOn
  have hd : ContinuousOn (fun w => fderiv ℂ G w v) U :=
    (hG.fderiv_of_isOpen (m := ∞) hU (by simp)).continuousOn.clm_apply continuousOn_const
  have heval (i : Fin n) : ContinuousOn (fun w => (fderiv ℂ G w v) i) U :=
    (contDiff_piLp_apply (𝕜 := ℂ) (n := ∞) (p := 2) (i := i)).continuous.comp_continuousOn hd
  have hmaps : MapsTo G U (chartTarget a) := by
    intro w hw
    exact (extChartAt (ComplexModel n) a).map_source (by simpa only [extChartAt_source, mem_preimage] using hw.2)
  have hm (i j : Fin n) : ContinuousOn (fun w => hMat k a (G w) i j) U :=
    (hMat_continuousOn k hk a i j).comp hG.continuousOn hmaps
  have hq : ContinuousOn (fun w =>
      (star (WithLp.ofLp (fderiv ℂ G w v)) ⬝ᵥ
        (hMat k a (G w) *ᵥ WithLp.ofLp (fderiv ℂ G w v))).re) U := by
    apply Complex.continuous_re.comp_continuousOn
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply]
    exact continuousOn_finset_sum _ fun i _ =>
      (Complex.continuous_conj.comp_continuousOn (heval i)).mul
        (continuousOn_finset_sum _ fun j _ => (hm i j).mul (heval j))
  have heq : ∀ w ∈ U,
      (star (WithLp.ofLp (fderiv ℂ G w v)) ⬝ᵥ
        (hMat k a (G w) *ᵥ WithLp.ofLp (fderiv ℂ G w v))).re =
      hermitianNormSq (k (Φ w))
        (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ w v) := by
    intro w hw
    have hsource : Φ w ∈ (extChartAt (ComplexModel n) a).source :=
      by simpa only [extChartAt_source, mem_preimage] using hw.2
    have hΦd := (hΦ.contMDiffAt (Metric.isOpen_ball.mem_nhds hw.1)).mdifferentiableAt (by simp)
    have hchain := mfderiv_comp (I := 𝓘(ℂ, ComplexVector n)) (I' := ComplexModel n)
      (I'' := 𝓘(ℂ, ComplexVector n)) w (mdifferentiableAt_extChartAt hw.2) hΦd
    have h := congrArg (fun L => L v) hchain
    rw [mfderiv_eq_fderiv] at h
    change fderiv ℂ G w v = tangentCoords a (Φ w)
      (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ w v) at h
    change (star (WithLp.ofLp (fderiv ℂ G w v)) ⬝ᵥ
      (hMat k a (chartPt a (Φ w)) *ᵥ WithLp.ofLp (fderiv ℂ G w v))).re = _
    rw [chart_quadratic_norm k a (Φ w) hsource, h,
      chartVec_tangentCoords a (Φ w) hsource]
  exact ((hq.congr (fun w hw => (heq w hw).symm)).continuousAt
    (hU.mem_nhds hwU)).continuousWithinAt

end Yau.Proofs.C07RadialCurveAux
