import Yau.Proofs.P02CurvaturePair
import Yau.LeafProofs.L23DistanceEnergyParallelSecond
import Yau.LeafProofs.L23DistanceEnergyRayIntegral

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P02Aux
open Yau Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

/-- The actual endpoint variation data used below.  Its witnesses are
constructed by `parallelEndpointVariation`, rather than postulated. -/
structure ParallelVariationData (h : HermitianField M) (γ : ℝ → M.Carrier)
    (δ : ℝ) (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier) : Prop where
  delta_pos : 0 < δ
  zero_source : (0 : ComplexVector n) ∈ e.source
  endpoint_zero : e 0 = γ 1
  smooth : letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n))
      𝓘(ℝ, ComplexVector n) 3 (Function.uncurry A)
      (Set.Ioo (-δ) (1+δ) ×ˢ e.source)
  inverse_smooth : letI := manifold_realSmooth M
    ContMDiffOn 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 3 e.symm e.target
  zero : ∀ u ∈ Set.Ioo (-δ) (1+δ), A u 0 = γ u
  endpoints : ∀ v ∈ e.source, A 0 v = γ 0 ∧ A 1 v = e v
  terminal_frame : (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1)
  pairing : ∀ u ∈ Set.Ioo (-δ) (1+δ), ∀ v w : ComplexVector n,
    (underlyingRealRiemannianMetric h).inner (γ u) (P u v) (P u w) =
      realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) v w
  jets : ∀ (c : M.Carrier) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) →
    γ u ∈ (extChartAt (ComplexModel n) c).source →
    (∀ w : ComplexVector n,
      HasDerivAt (fun s => realTangentCoords c (γ s) (P s w))
        (-chartChristoffelBilin h c (chartPt c (γ u))
          (geoChartState γ c u).2 (realTangentCoords c (γ u) (P u w))) u) ∧
    HasFDerivAt (fun v => chartPt c (A u v))
      (u • ((realTangentCoords c (γ u)).comp (P u).toContinuousLinearMap)) 0 ∧
    (∀ w : ComplexVector n,
      HasDerivAt (deriv (fun r : ℝ => chartPt c (A u (r • w))))
        (-chartChristoffelBilin h c (chartPt c (γ u))
          (u • realTangentCoords c (γ u) (P u w))
          (u • realTangentCoords c (γ u) (P u w))) 0)

theorem exists_parallelVariationData (h : HermitianField M) (hs : MetricSmooth h)
    (γ : ℝ → M.Carrier) (ε : ℝ) (hε : 0 < ε)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-ε) (1+ε))) :
    ∃ δ e P A, δ < ε ∧ ParallelVariationData h γ δ e P A := by
  letI := manifold_realSmooth M
  obtain ⟨δ,e,P,A,hδ,hδε,h0,he0,hA,he,hA0,hend,hP1,hpair,hjets⟩ :=
    parallelEndpointVariation n M h hs Set.univ isOpen_univ γ ε hε hγ
      (fun _ _ => Set.mem_univ _)
  exact ⟨δ,e,P,A,hδε,hδ,h0,he0,hA,he,hA0,
    fun v hv => ⟨(hend v hv).1,(hend v hv).2.1⟩,hP1,hpair,hjets⟩

def parallelBisectional (h : HermitianField M) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (w : ComplexVector n) (u : ℝ) : ℝ :=
  coordinateBisectional h (γ u) (chartPt (γ u) (γ u))
    (geoChartState γ (γ u) u).2 (realTangentCoords (γ u) (γ u) (P u w))

theorem parallel_secondDensity_pair (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier)
    (H : ParallelVariationData h γ δ e P A)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (w : ComplexVector n) (u : ℝ) (hu : u ∈ Set.Ioo (-δ) (1+δ)) :
    deriv (deriv (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u^2)) 0 +
      deriv (deriv (fun r : ℝ => fieldPathSpeed h
        (fun s => A s (r • (Complex.I • w))) u^2)) 0 =
      4 * realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) w w -
        2 * u^2 * parallelBisectional h γ P w u := by
  letI := manifold_realSmooth M
  let c := γ u
  have hc : γ u ∈ (chartAt (ComplexVector n) c).source := mem_chart_source _ _
  have hc' : γ u ∈ (extChartAt (ComplexModel n) c).source := mem_extChartAt_source c
  have hz : chartPt c (γ u) ∈ chartTarget c :=
    (extChartAt (ComplexModel n) c).map_source hc'
  have hP (c : M.Carrier) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) (1+δ))
      (hc : γ t ∈ (chartAt (ComplexVector n) c).source) :=
    (H.jets c t ht (by simpa only [extChartAt_source] using hc)).1
  have hFirst (c : M.Carrier) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) (1+δ))
      (hc : γ t ∈ (chartAt (ComplexVector n) c).source) :=
    (H.jets c t ht (by simpa only [extChartAt_source] using hc)).2.1
  have hSecond (c : M.Carrier) (t : ℝ) (ht : t ∈ Set.Ioo (-δ) (1+δ))
      (hc : γ t ∈ (chartAt (ComplexVector n) c).source) :=
    (H.jets c t ht (by simpa only [extChartAt_source] using hc)).2.2
  rw [fieldPathSpeedSq_parallelVariation_secondDeriv h hs γ P A δ H.delta_pos
    e.source e.open_source H.zero_source hγ H.zero hP hFirst hSecond u hu c hc w H.smooth,
    fieldPathSpeedSq_parallelVariation_secondDeriv h hs γ P A δ H.delta_pos
    e.source e.open_source H.zero_source hγ H.zero hP hFirst hSecond u hu c hc
      (Complex.I • w) H.smooth]
  have hJ : realTangentCoords c (γ u) (P u (Complex.I • w)) =
      Complex.I • realTangentCoords c (γ u) (P u w) := by
    rw [parallel_frame_I h hs hk γ δ H.delta_pos hγ P H.terminal_frame
      (fun c t ht hc => (H.jets c t ht hc).1) u hu w,
      realTangentCoords_realTangentJ c (γ u) hc]
  have hQ : realMetricInChart h c (chartPt c (γ u))
      (realTangentCoords c (γ u) (P u w)) (realTangentCoords c (γ u) (P u w)) =
      realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) w w := by
    rw [realMetricInChart_tangentCoords h c (γ u) hc]
    exact H.pairing u hu w w
  rw [hJ, realMetricInChart_I_I h c hz, hQ]
  simp only [connectionCurvature_smul_first_third, map_smul, smul_eq_mul]
  have HB := connectionCurvature_bisectional_sign h hs c hz
    (geoChartState γ c u).2 (realTangentCoords c (γ u) (P u w))
  dsimp only [parallelBisectional, c] at *
  nlinarith [HB]

theorem parallel_energy_pair (h : HermitianField M)
    (hs : MetricSmooth h) (hk : KahlerClosed h)
    (γ : ℝ → M.Carrier) (δ : ℝ)
    (e : OpenPartialHomeomorph (ComplexVector n) M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ]
      TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier)
    (H : ParallelVariationData h γ δ e P A)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ))) (w : ComplexVector n) :
    IntegrableOn (fun u => u^2 * parallelBisectional h γ P w u) (Set.Icc (0 : ℝ) 1) ∧
    deriv (deriv (fun r : ℝ => fieldPathEnergy h (fun u => A u (r • w)))) 0 +
      deriv (deriv (fun r : ℝ => fieldPathEnergy h
        (fun u => A u (r • (Complex.I • w))))) 0 =
      4 * realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) w w -
        2 * ∫ u in Set.Icc (0 : ℝ) 1, u^2 * parallelBisectional h γ P w u := by
  letI := manifold_realSmooth M
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ Set.Ioo (-δ) (1+δ) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2, H.delta_pos]
  let D := fun v u => deriv (deriv (fun r : ℝ =>
    fieldPathSpeed h (fun s => A s (r • v)) u^2)) 0
  let Q := realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) w w
  have hi (v : ComplexVector n) : IntegrableOn (D v) (Set.Icc (0 : ℝ) 1) :=
    rayEnergy_secondDensity_integrableOn h hs A _ _ isOpen_Ioo e.open_source
      hunit H.zero_source v H.smooth
  have hpair (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      D w u + D (Complex.I • w) u = 4*Q-2*(u^2*parallelBisectional h γ P w u) := by
    simpa only [D, Q, mul_assoc] using
      parallel_secondDensity_pair h hs hk γ δ e P A H hγ w u (hunit hu)
  have hB : IntegrableOn (fun u => u^2 * parallelBisectional h γ P w u)
      (Set.Icc (0 : ℝ) 1) := by
    have hc : IntegrableOn (fun _ : ℝ => 4*Q) (Set.Icc (0 : ℝ) 1) :=
      continuous_const.integrableOn_Icc
    have H' := (hc.sub ((hi w).add (hi (Complex.I • w)))).div_const 2
    apply H'.congr
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    have HH := hpair u hu
    change (4*Q-(D w u+D (Complex.I • w) u))/2 = _
    linarith
  refine ⟨hB, ?_⟩
  rw [rayEnergy_secondDeriv_eq_integral h hs A _ _ isOpen_Ioo e.open_source hunit
    H.zero_source w H.smooth,
    rayEnergy_secondDeriv_eq_integral h hs A _ _ isOpen_Ioo e.open_source hunit
    H.zero_source (Complex.I • w) H.smooth, ← integral_add (hi w) (hi (Complex.I • w))]
  calc
    _ = ∫ u in Set.Icc (0 : ℝ) 1, 4*Q-2*(u^2*parallelBisectional h γ P w u) := by
      apply setIntegral_congr_fun measurableSet_Icc
      exact hpair
    _ = _ := by
      have hc : IntegrableOn (fun _ : ℝ => 4*Q) (Set.Icc (0 : ℝ) 1) :=
        continuous_const.integrableOn_Icc
      rw [integral_sub hc (hB.const_mul 2)]
      rw [integral_const_mul, setIntegral_const, measureReal_def, Real.volume_Icc]
      norm_num
      rw [integral_const_mul]

end Yau.NodeProofs.P02Aux
