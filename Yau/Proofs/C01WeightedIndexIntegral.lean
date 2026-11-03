import Yau.Proofs.C01WeightedParallelDensity
import Yau.Proofs.C01WeightedPhysicalTrace
import Yau.Proofs.C01IndexTraceIntegral
import Yau.LeafProofs.L23FieldMetricParallelVariation

/-! Fixed-endpoint actual energy minima and the exact physical second-variation trace give the weighted index integral inequality. -/

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.C01Aux
open Yau Yau.Blueprint Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.LeafProofs.L23LocalDistanceContract
variable {n : ℕ} {M : ComplexManifold n}

theorem minimizing_field_geodesic_weighted_index
    (k : HermitianField M) (hk : MetricSmooth k) (γ : ℝ → M.Carrier)
    (ε : ℝ) (hε : 0 < ε) (hγ : FieldGeodesicOn k γ (Set.Ioo (-ε) (1+ε)))
    (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1,
      realTangentSpeedSq k (γ u) (realCurveVelocity γ u) = inducedDistance k (γ 0) (γ 1) ^ 2)
    (hR : ContinuousOn (fun u => actualRealRicciQuadratic k (γ u) (realCurveVelocity γ u))
      (Set.Icc (0 : ℝ) 1))
    (κ Dcost : ℝ) (hκ : 0 < κ)
    (hcost : (∫ u in Set.Icc (0 : ℝ) 1, deriv (indexCutoff κ) u ^ 2) ≤ Dcost / κ) :
    (∫ u in Set.Icc (0 : ℝ) 1, indexCutoff κ u ^ 2 *
      actualRealRicciQuadratic k (γ u) (realCurveVelocity γ u)) ≤ (2*n : ℕ) * Dcost / κ := by
  letI := manifold_realSmooth M
  obtain ⟨δ, e, P, A, hδ, hδε, hzero, hezero, hA, heinv, hA0, hAends, hP1, hPair, hJets⟩ :=
    parallelEndpointVariation n M k hk Set.univ isOpen_univ γ ε hε hγ (fun _ _ => Set.mem_univ _)
  let J := Set.Ioo (-δ) (1+δ)
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ J := by intro u hu; constructor <;> linarith [hu.1, hu.2]
  have hsubε : J ⊆ Set.Ioo (-ε) (1+ε) := by
    intro u hu
    constructor <;> linarith [hu.1, hu.2]
  have hγδ : FieldGeodesicOn k γ J :=
    ⟨hγ.1.mono hsubε, fun c u hu hc => hγ.2 c u (hsubε hu) hc⟩
  have HP (c : M.Carrier) (u : ℝ) (hu : u ∈ J)
      (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).1
  have HF (c : M.Carrier) (u : ℝ) (hu : u ∈ J)
      (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).2.1
  have HS (c : M.Carrier) (u : ℝ) (hu : u ∈ J)
      (hc : γ u ∈ (chartAt (ComplexVector n) c).source) :=
    (hJets c u hu (by simpa only [extChartAt_source] using hc)).2.2
  obtain ⟨J', U', hJ', hU', hunit', hzero', hmap⟩ := exists_weightedVariation_domain
    (indexCutoffRatio κ) (indexCutoffRatio_contDiff hκ).continuous J e.source
    isOpen_Ioo e.open_source hunit hzero
  have hsub : J' ⊆ J := fun u hu =>
    (hmap (show (u, (0 : ComplexVector n)) ∈ J' ×ˢ U' from ⟨hu, hzero'⟩)).1
  let B := weightedVariation A (indexCutoffRatio κ)
  have hB := weightedVariation_contMDiffOn A (indexCutoffRatio κ)
    ((indexCutoffRatio_contDiff hκ).of_le (by simp)) J J' e.source U' hmap hA
  have hbase (s : ℝ) (hs : s ∈ J') : B s 0 = γ s := by
    simp only [B, weightedVariation, smul_zero, hA0 s (hsub hs)]
  let b := fieldOrthonormalFrame k (γ 1)
  let W := fun i : Fin (2*n) => realTangentCoords (γ 1) (γ 1) (b i)
  let F := fun (i : Fin (2*n)) (r u : ℝ) => B u (r • W i)
  let R := fun u => actualRealRicciQuadratic k (γ u) (realCurveVelocity γ u)
  let D := fun (i : Fin (2*n)) (u : ℝ) =>
    deriv (deriv (fun r => actualPathSpeed k (F i r) u ^ 2)) 0
  have hF (i : Fin (2*n)) :
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ComplexVector n) 3 (Function.uncurry (F i))
        (rayParameterDomain U' (W i) ×ˢ J') := rayFamily_contMDiffOn B J' U' (W i) hB
  have hI (i : Fin (2*n)) := rayParameterDomain_isOpen U' hU' (W i)
  have hIzero (i : Fin (2*n)) := rayParameterDomain_zero_mem U' hzero' (W i)
  have hD (i : Fin (2*n)) : IntegrableOn (D i) (Set.Icc (0 : ℝ) 1) volume :=
    second_parameter_density_integrableOn_unit (staticPathEnergyDensity k (F i))
      (rayParameterDomain U' (W i)) J' (hI i) hJ' hunit'
      (staticPathEnergyDensity_contDiffOn_two k hk (F i) _ J' (hI i) hJ' (hF i)) 0 (hIzero i)
  have hpositive (i : Fin (2*n)) : 0 ≤ ∫ u in Set.Icc (0 : ℝ) 1, D i u := by
    have harg : ContDiffOn ℝ 3 (fun u : ℝ => ((0 : ℝ), u)) J' :=
      contDiffOn_const.prodMk contDiffOn_id
    have hF0 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 (F i 0) J' :=
      ((hF i).comp harg.contMDiffOn (fun u hu => ⟨hIzero i, hu⟩)).of_le (by norm_num)
    have hγ1 : ContMDiffOn 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ J' :=
      (hγδ.1.mono hsub).of_le (by norm_num)
    have hnear (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : F i 0 =ᶠ[𝓝 u] γ := by
      filter_upwards [hJ'.mem_nhds (hunit' hu)] with s hs
      simpa only [F, zero_smul] using hbase s hs
    have HE : actualPathEnergy k (F i 0) = inducedDistance k (γ 0) (γ 1) ^ 2 :=
      (actualPathEnergy_congr_unit_germs k (F i 0) γ hnear
        (fun u hu => (hF0 u (hunit' hu)).contMDiffAt (hJ'.mem_nhds (hunit' hu)))
        (fun u hu => (hγ1 u (hunit' hu)).contMDiffAt (hJ'.mem_nhds (hunit' hu)))).trans
          (actualPathEnergy_eq_of_constant_speedSq k γ _ hspeed)
    have hends (r : ℝ) (_hr : r ∈ rayParameterDomain U' (W i)) :
        F i r 0 = γ 0 ∧ F i r 1 = γ 1 := by
      obtain ⟨hψ0, hψ1⟩ := indexCutoffRatio_endpoints hκ
      exact weightedVariation_endpoints A (indexCutoffRatio κ) (γ 0) (γ 1) hψ0 hψ1
        (hA0 0 (hunit (by norm_num))) (hA0 1 (hunit (by norm_num))) (r • W i)
    have H := actualEnergy_secondVariation_nonneg_on_open_unit k hk (F i)
      (rayParameterDomain U' (W i)) J' (hI i) hJ' (hIzero i) hunit' (γ 0) (γ 1) hends HE (hF i)
    rw [actualPathEnergy_second_derivative_eq_integral k hk (F i) _ J' (hI i) hJ' hunit'
      0 (hIzero i) (hF i)] at H
    exact H
  have htrace (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) :
      (∑ i, D i u) = 2 * (Fintype.card (Fin (2*n)) : ℝ) * deriv (indexCutoff κ) u ^ 2 -
        2 * (indexCutoff κ u ^ 2 * R u) := by
    have hγAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u :=
      ((hγδ.1 u (hunit hu)).contMDiffAt (isOpen_Ioo.mem_nhds (hunit hu))).of_le (by norm_num)
    have HC : ContMDiffAt 𝓘(ℝ, ComplexVector n) 𝓘(ℝ, ComplexVector n) 1
        (chartPt (γ u)) (γ u) := by
      convert! (contMDiffAt_extChartAt' (I := 𝓘(ℝ, ComplexVector n)) (n := 1)
        (x := γ u) (x' := γ u) (mem_chart_source _ _)) using 1
    have HD := ((HC.comp u hγAt).contDiffAt.differentiableAt (by norm_num)).hasDerivAt
    have HT : realTangentCoords (γ u) (γ u) (realCurveVelocity γ u) = (geoChartState γ (γ u) u).2 :=
      realCurveVelocity_coords_of_hasDerivAt γ u (γ u) _ (mem_chart_source _ _)
        (hγAt.mdifferentiableAt (by norm_num)) HD
    have H := weighted_secondDensity_physical_trace k hk (γ 1) (γ u) (P u)
      (hPair u (hunit hu)) (realCurveVelocity γ u) (indexCutoff κ u)
      (deriv (indexCutoff κ) u) b (fun i => D i u) (fun i => by
        have H := indexWeighted_parallel_density_second_derivative k hk γ P A δ hδ e.source
          e.open_source hγδ hA0 HP HF HS κ hκ J' U' hJ' hU' hzero' hmap u (hunit' hu)
          (γ u) (mem_chart_source _ _) (W i) hA
        simpa only [F, B, D, W, HT] using H)
    simpa only [Fintype.card_fin, R, mul_assoc] using H
  have hweighted : IntegrableOn (fun u => indexCutoff κ u ^ 2 * R u)
      (Set.Icc (0 : ℝ) 1) volume :=
    (((indexCutoff_contDiff κ).continuous.pow 2).continuousOn.mul hR).integrableOn_compact isCompact_Icc
  have H := indexCutoff_weighted_integral_bound D R κ Dcost hκ hD hweighted hpositive htrace hcost
  simpa only [Fintype.card_fin] using H

end Yau.NodeProofs.C01Aux
