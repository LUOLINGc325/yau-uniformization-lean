import Yau.LeafProofs.L23FieldMetricNormalInversePath
import Yau.LeafProofs.L23FieldMetricUnitLength

/-! Local normal coordinates identify the original global length distance. -/
noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold ENNReal
namespace Yau.LeafProofs.L23Aux
open L12Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option maxHeartbeats 800000

theorem normalEndpoint_distance_on_metric_ball
    (h : HermitianField M) (hh : MetricSmooth h) (c : M.Carrier)
    (B : Set (ComplexVector n)) (hB : IsOpen B) (hBsub : B ⊆ chartTarget c)
    {ρ ε δ : ℝ} (hρ : 0 < ρ) (hε : 0 < ε) (hδ : 0 < δ)
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
    (z : ComplexVector n) (hz : z ∈ B) (hzero : (η (z,0) 1).1 = z)
    (hball : ∀ y : M.Carrier, inducedDistance h (chartInv c z) y < δ →
      y ∈ (chartAt (ComplexVector n) c).source ∧ (z,chartPt c y) ∈ e.target)
    (y : M.Carrier) (hy : inducedDistance h (chartInv c z) y < δ) :
    inducedDistance h (chartInv c z) y =
      chartVectorNorm h c z (e.symm (z,chartPt c y)).2 := by
  letI := manifold_realSmooth M
  letI := metricSpaceOfField h hh
  letI : ∀ q : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) q) :=
    fun q => underlyingRealTangentNormedAddCommGroup h q
  letI : ∀ q : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) q) :=
    fun q => underlyingRealTangentInnerProductSpace h q
  let x := chartInv c z
  let v := (e.symm (z,chartPt c y)).2
  have Hy := hball y hy
  have Hfiber := endpoint_inverse_fiber e (fun p => (η p 1).1) he Hy.2
  have hp : (z,v) ∈ B ×ˢ Metric.ball (0 : ComplexVector n) ρ := by
    rw [← hsource]
    exact Hfiber.2.1
  have hinvy : chartInv c (chartPt c y) = y :=
    (extChartAt (ComplexModel n) c).left_inv (by simpa only [extChartAt_source] using Hy.1)
  have hinit : η (z,v) 0 = (z,v) := hi _ hp
  have hupper : inducedDistance h x y ≤ chartVectorNorm h c z v := by
    have H := inducedDistance_chartGeodesic_unit_le h hh c (η (z,v)) hε (hs _ hp)
    rw [hinit,Hfiber.2.2,hinvy] at H
    exact H
  apply le_antisymm hupper
  by_contra! hsmall
  let r := chartVectorNorm h c z v
  obtain ⟨a,hda,harδ⟩ := exists_between (lt_min hsmall hy)
  have har : a < r := harδ.trans_le (min_le_left _ _)
  have haδ : a < δ := harδ.trans_le (min_le_right _ _)
  have ha : 0 < a := (inducedDistance_nonneg h hh x y).trans_lt hda
  have hnear : Manifold.riemannianEDist 𝓘(ℝ, ComplexVector n) x y < ENNReal.ofReal a := by
    rw [← inducedDistance_eq_riemannianEDist h hh]
    exact (ENNReal.ofReal_lt_ofReal_iff ha).mpr hda
  obtain ⟨β,hβ0,hβ1,hβ,hlen,_,_⟩ :=
    Manifold.exists_lt_locally_constant_of_riemannianEDist_lt hnear zero_lt_one
  have hinside (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : inducedDistance h x (β u) < δ := by
    have HD : ENNReal.ofReal (inducedDistance h x (β u)) ≤
        Manifold.pathELength 𝓘(ℝ, ComplexVector n) β 0 u := by
      rw [inducedDistance_eq_riemannianEDist h hh]
      exact Manifold.riemannianEDist_le_pathELength hβ.contMDiffOn hβ0 rfl hu.1
    have Hmon : Manifold.pathELength 𝓘(ℝ, ComplexVector n) β 0 u ≤
        Manifold.pathELength 𝓘(ℝ, ComplexVector n) β 0 1 :=
      Manifold.pathELength_mono le_rfl hu.2
    exact ((ENNReal.ofReal_lt_ofReal_iff ha).mp ((HD.trans Hmon).trans_lt hlen)).trans haδ
  let d := (r-a)/2
  have hd : 0 < d := by dsimp [d]; linarith
  have HFTC := normalEndpoint_inverse_radius_sub_le_pathELength h hh c B hB hε hd η e
    hsource he hinv hη hi hs z β 0 1 zero_le_one hβ (fun u hu => hball _ (hinside u hu))
  have hzeroSource : (z,(0 : ComplexVector n)) ∈ e.source := by
    rw [hsource]
    exact ⟨hz,Metric.mem_ball_self hρ⟩
  have hezero : e (z,0) = (z,z) := (he hzeroSource).trans (by
    change (z,(η (z,0) 1).1) = (z,z)
    rw [hzero])
  have hxcoord : chartPt c x = z := (extChartAt (ComplexModel n) c).right_inv (hBsub hz)
  have hxinv : e.symm (z,chartPt c x) = (z,0) := by
    rw [hxcoord,← hezero,e.left_inv hzeroSource]
  have hR0 : regularizedChartRadius h c z d (e.symm (z,chartPt c (β 0))).2 = d := by
    rw [hβ0,hxinv]
    simp only [regularizedChartRadius,map_zero,ContinuousLinearMap.zero_apply,zero_add]
    exact Real.sqrt_sq hd.le
  have hR1 : r ≤ regularizedChartRadius h c z d (e.symm (z,chartPt c (β 1))).2 := by
    rw [hβ1]
    exact chartVectorNorm_le_regularizedChartRadius h c z v d
  have hR : a < regularizedChartRadius h c z d (e.symm (z,chartPt c (β 1))).2-
      regularizedChartRadius h c z d (e.symm (z,chartPt c (β 0))).2 := by
    rw [hR0]
    dsimp only [d]
    linarith
  have HLT := (ENNReal.ofReal_lt_ofReal_iff (ha.trans hR)).mpr hR
  exact (not_lt_of_ge HFTC) (hlen.trans HLT)

end Yau.LeafProofs.L23Aux
