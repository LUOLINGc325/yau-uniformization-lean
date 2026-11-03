import Yau.Proofs.C06Density
import Yau.LeafProofs.L23FieldMetricGeodesicEnergy

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff Manifold
namespace Yau.Proofs.C06Aux
open Yau Yau.Blueprint Yau.NodeProofs Yau.NodeProofs.P07DistanceLevi
open Yau.LeafProofs L12Aux L23Aux L23LocalDistanceContract
variable {n : ℕ}

theorem parallelVariation_paired_energySecond_lt
    (X : KahlerManifold n) (γ : ℝ → Pt X)
    (P : (u : ℝ) → ComplexVector n ≃L[ℝ] TangentSpace 𝓘(ℝ, ComplexVector n) (γ u))
    (A : ℝ → ComplexVector n → Pt X) (δ : ℝ) (hδ : 0 < δ)
    (U : Set (ComplexVector n)) (hU : IsOpen U) (hzero : (0 : ComplexVector n) ∈ U)
    (hγ : FieldGeodesicOn X.metric.form γ (Set.Ioo (-δ) (1+δ)))
    (hA0 : ∀ u ∈ Set.Ioo (-δ) (1+δ), A u 0 = γ u)
    (hP1 : (P 1).toContinuousLinearMap = realFrameCLM (γ 1) (γ 1))
    (hPair : ∀ u ∈ Set.Ioo (-δ) (1+δ), ∀ v w : ComplexVector n,
      (underlyingRealRiemannianMetric X.metric.form).inner (γ u) (P u v) (P u w) =
        realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v w)
    (hP : ∀ (c : Pt X) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) →
      γ u ∈ (chartAt (ComplexVector n) c).source → ∀ w : ComplexVector n,
      HasDerivAt (fun s => realTangentCoords c (γ s) (P s w))
        (-chartChristoffelBilin X.metric.form c (chartPt c (γ u)) (geoChartState γ c u).2
          (realTangentCoords c (γ u) (P u w))) u)
    (hFirst : ∀ (c : Pt X) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) →
      γ u ∈ (chartAt (ComplexVector n) c).source →
      HasFDerivAt (fun v => chartPt c (A u v))
        (u • ((realTangentCoords c (γ u)).comp (P u).toContinuousLinearMap)) 0)
    (hSecond : ∀ (c : Pt X) (u : ℝ), u ∈ Set.Ioo (-δ) (1+δ) →
      γ u ∈ (chartAt (ComplexVector n) c).source → ∀ w : ComplexVector n,
      HasDerivAt (deriv (fun r : ℝ => chartPt c (A u (r • w))))
        (-chartChristoffelBilin X.metric.form c (chartPt c (γ u))
          (u • realTangentCoords c (γ u) (P u w))
          (u • realTangentCoords c (γ u) (P u w))) 0)
    (d : ℝ) (hd : 0 < d)
    (hspeed : ∀ u ∈ Set.Icc (0 : ℝ) 1, actualSpeedSq X.metric.form γ u = d ^ 2)
    (v : ComplexVector n) (hv : v ≠ 0) :
    letI := manifold_realSmooth X.manifold
    ContMDiffOn (𝓘(ℝ, ℝ).prod 𝓘(ℝ, ComplexVector n)) 𝓘(ℝ, ComplexVector n) 3
      (Function.uncurry A) (Set.Ioo (-δ) (1+δ) ×ˢ U) →
    deriv (deriv (fun r : ℝ => fieldPathEnergy X.metric.form (fun s => A s (r • v)))) 0 +
      deriv (deriv (fun r : ℝ => fieldPathEnergy X.metric.form
        (fun s => A s (r • (Complex.I • v))))) 0 <
      4 * realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v v := by
  letI := manifold_realSmooth X.manifold
  intro hA
  have hh := metricSmooth_of_smoothMetric X.metric
  let J := Set.Ioo (-δ) (1 + δ)
  have hunit : Set.Icc (0 : ℝ) 1 ⊆ J := by
    intro u hu; constructor <;> linarith [hu.1, hu.2]
  let D : ℝ → ℝ := fun u =>
    deriv (deriv (fun r : ℝ => fieldPathSpeed X.metric.form (fun s => A s (r • v)) u ^ 2)) 0 +
      deriv (deriv (fun r : ℝ => fieldPathSpeed X.metric.form
        (fun s => A s (r • (Complex.I • v))) u ^ 2)) 0
  let B := 4 * realMetricInChart X.metric.form (γ 1) (chartPt (γ 1) (γ 1)) v v
  have hi₁ := rayEnergy_secondDensity_integrableOn X.metric.form hh A J U isOpen_Ioo hU
    hunit hzero v hA
  have hi₂ := rayEnergy_secondDensity_integrableOn X.metric.form hh A J U isOpen_Ioo hU
    hunit hzero (Complex.I • v) hA
  have hiD : IntegrableOn D (Set.Icc (0 : ℝ) 1) := hi₁.add hi₂
  have hle (u : ℝ) (hu : u ∈ Set.Icc (0 : ℝ) 1) : D u ≤ B :=
    parallelVariation_paired_secondDensity_le X γ P A δ hδ U hU hzero hγ hA0 hP1 hPair
      hP hFirst hSecond u (hunit hu) v hA
  have hlt (u : ℝ) (hu : u ∈ Set.Ioo (0 : ℝ) 1) : D u < B := by
    have hu' : u ∈ Set.Icc (0 : ℝ) 1 := ⟨hu.1.le, hu.2.le⟩
    have hAt : ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ u :=
      ((hγ.1 u (hunit hu')).contMDiffAt (isOpen_Ioo.mem_nhds (hunit hu'))).of_le (by norm_num)
    have he := actualSpeedSq_eq_chartEnergy X.metric.form γ (γ u) u (mem_chart_source _ _) hAt
    have hG := he.symm.trans (hspeed u hu')
    have hT : (geoChartState γ (γ u) u).2 ≠ 0 := by
      intro hz
      change realMetricInChart X.metric.form (γ u) (chartPt (γ u) (γ u))
        (geoChartState γ (γ u) u).2 (geoChartState γ (γ u) u).2 = d ^ 2 at hG
      simp only [hz, map_zero, ContinuousLinearMap.zero_apply] at hG
      nlinarith [sq_pos_of_pos hd]
    exact parallelVariation_paired_secondDensity_lt X γ P A δ hδ U hU hzero hγ hA0 hP1
      hPair hP hFirst hSecond u (hunit hu') v hT hv (ne_of_gt hu.1) hA
  have hconst : IntegrableOn (fun _ : ℝ => B) (Set.Icc (0 : ℝ) 1) :=
    integrableOn_const (hs := by simp)
  have hleAE : D ≤ᵐ[volume.restrict (Set.Icc (0 : ℝ) 1)] (fun _ => B) := by
    filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
    exact hle u hu
  have hint : (∫ u in Set.Icc (0 : ℝ) 1, D u) < ∫ _u in Set.Icc (0 : ℝ) 1, B := by
    apply lt_of_le_of_ne (integral_mono_ae hiD hconst hleAE)
    intro heq
    have heqAE := (integral_eq_iff_of_ae_le hiD hconst hleAE).mp heq
    have hmem : ∀ᵐ u ∂volume.restrict (Set.Icc (0 : ℝ) 1), u ∈ Set.Ioo (0 : ℝ) 1 := by
      rw [← Measure.restrict_congr_set (Ioo_ae_eq_Icc (μ := volume))]
      exact ae_restrict_mem measurableSet_Ioo
    have hfalse : ∀ᵐ u ∂volume.restrict (Set.Icc (0 : ℝ) 1), False := by
      filter_upwards [heqAE, hmem] with u hueq hu
      exact (hlt u hu).ne hueq
    change (∅ : Set ℝ) ∈ ae (volume.restrict (Set.Icc (0 : ℝ) 1)) at hfalse
    have H : (volume : Measure ℝ) (Set.Icc (0 : ℝ) 1) = 0 :=
      ae_restrict_eq_bot.mp (Filter.empty_mem_iff_bot.mp hfalse)
    norm_num at H
  rw [rayEnergy_secondDeriv_eq_integral X.metric.form hh A J U isOpen_Ioo hU hunit hzero v hA,
    rayEnergy_secondDeriv_eq_integral X.metric.form hh A J U isOpen_Ioo hU hunit hzero
      (Complex.I • v) hA, ← integral_add hi₁ hi₂]
  simpa [D, B, integral_const, Measure.real] using hint

end Yau.Proofs.C06Aux
