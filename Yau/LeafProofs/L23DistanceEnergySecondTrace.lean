import Yau.LeafProofs.L23DistanceEnergyIntegralBound
import Yau.LeafProofs.L23DistanceEnergyTransportTrace
import Yau.LeafProofs.L23DistanceEnergyParallelSecond
import Yau.LeafProofs.L23FieldMetricGeodesicEnergy

/-! Integrating the actual parallel-frame second variations gives the local trace constant. -/

noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux L23LocalDistanceContract
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2200000

variable {n : ℕ} {M : ComplexManifold n}

theorem energySecondTrace_bound_of_densityFormula
    (h : HermitianField M) (hh : MetricSmooth h) (γ : ℝ → M.Carrier)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → M.Carrier) (δ K d : ℝ) (hδ : 0<δ)
    (U : Set (ComplexVector n)) (hU : IsOpen U) (hzero : (0 : ComplexVector n)∈U)
    (hγ : FieldGeodesicOn h γ (Set.Ioo (-δ) (1+δ)))
    (hPair : ∀ u∈Set.Icc (0 : ℝ) 1, ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric h).inner (γ u) (P u v) (P u w)=
        realMetricInChart h (γ 1) (chartPt (γ 1) (γ 1)) v w)
    (hcurv : ∀ u∈Set.Icc (0 : ℝ) 1, curvatureJetNorm h 0 (γ u)≤K)
    (hspeed : ∀ u∈Set.Icc (0 : ℝ) 1, actualSpeedSq h γ u=d^2)
    (b : letI := underlyingRealTangentNormedAddCommGroup h (γ 1)
      letI := underlyingRealTangentInnerProductSpace h (γ 1)
      OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) (γ 1)))
    (hFormula : ∀ u∈Set.Icc (0 : ℝ) 1, ∀ i : Fin (2*n),
      let w := realTangentCoords (γ 1) (γ 1) (b i)
      let V := realTangentCoords (γ u) (γ u) (P u w)
      let T := (geoChartState γ (γ u) u).2
      deriv (deriv (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • w)) u^2)) 0=
        2*realMetricInChart h (γ u) (chartPt (γ u) (γ u)) V V+
        2*realMetricInChart h (γ u) (chartPt (γ u) (γ u)) T
          (connectionCurvature (chartChristoffelBilin h (γ u)) (chartPt (γ u) (γ u)) (u • V) T (u • V))) :
    letI := manifold_realSmooth M
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ U) →
    (∑ i : Fin (2*n), deriv (deriv (fun r : ℝ => fieldPathEnergy h
      (fun u => A u (r • realTangentCoords (γ 1) (γ 1) (b i))))) 0)≤
        2*(2*n : ℕ)+(2/3 : ℝ)*(2*n : ℕ)*K*d^2 := by
  letI := manifold_realSmooth M
  intro hA
  let J := Set.Ioo (-δ) (1+δ)
  let W : Fin (2*n) → ComplexVector n := fun i => realTangentCoords (γ 1) (γ 1) (b i)
  let D : Fin (2*n) → ℝ → ℝ := fun i u =>
    deriv (deriv (fun r : ℝ => fieldPathSpeed h (fun s => A s (r • W i)) u^2)) 0
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ J := by intro u hu; constructor <;> linarith [hu.1,hu.2]
  have hD (i : Fin (2*n)) : IntegrableOn (D i) (Set.Icc (0 : ℝ) 1) :=
    rayEnergy_secondDensity_integrableOn h hh A J U isOpen_Ioo hU hunit hzero (W i) hA
  have hTrace (u : ℝ) (hu : u∈Set.Icc (0 : ℝ) 1) :
      (∑ i,D i u)≤2*(2*n : ℕ)+2*u^2*(2*n : ℕ)*K*d^2 := by
    have hγAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u :=
      ((hγ.1 u (hunit hu)).contMDiffAt (isOpen_Ioo.mem_nhds (hunit hu))).of_le (by norm_num)
    have he := actualSpeedSq_eq_chartEnergy h γ (γ u) u (mem_chart_source _ _) hγAt
    have hGspeed : realMetricInChart h (γ u) (chartPt (γ u) (γ u))
        (geoChartState γ (γ u) u).2 (geoChartState γ (γ u) u).2=d^2 :=
      he.symm.trans (hspeed u hu)
    exact parallelSecondDensity_trace_le h hh (γ 1) (γ u) (P u) (hPair u hu)
      (geoChartState γ (γ u) u).2 u K d (hcurv u hu) hGspeed b (fun i => D i u) (hFormula u hu)
  have H := integral_secondDensity_trace_bound (2*n : ℕ) K d D hD hTrace
  convert H using 1
  apply Finset.sum_congr rfl
  intro i _
  exact rayEnergy_secondDeriv_eq_integral h hh A J U isOpen_Ioo hU hunit hzero (W i) hA

end Yau.LeafProofs.L23Aux
