import Yau.Proofs.P07DistanceLeviParallel
import Yau.Proofs.P07DistanceLeviRankOne

noncomputable section
open Filter
open scoped Topology ContDiff Manifold

namespace Yau.NodeProofs.P07DistanceLevi
open Yau Yau.Blueprint Yau.LeafProofs L12Aux L18Aux L22Aux

theorem leviDirection_comp_holomorphic {n m : ℕ}
    {T : ComplexVector n → ComplexVector m} {f : ComplexVector m → ℝ}
    {z : ComplexVector n} (hT : ContDiffAt ℂ 2 T z)
    (hf : ContDiffAt ℝ 2 f (T z)) (v : ComplexVector n) :
    leviDirection (leviC (f ∘ T) z) v =
      leviDirection (leviC f (T z)) (fderiv ℂ T z v) := by
  rw [leviDirection, leviC_quadratic_re (hf.comp z (hT.restrict_scalars ℝ)),
    complexLeviQuadratic_comp hT hf, leviDirection, leviC_quadratic_re hf]

theorem directionalRankOne_comp_holomorphic {n m : ℕ}
    {T : ComplexVector n → ComplexVector m} {f : ComplexVector m → ℝ}
    {z : ComplexVector n} (hT : DifferentiableAt ℂ T z)
    (hf : DifferentiableAt ℝ f (T z)) (v : ComplexVector n) :
    directionalRankOne (f ∘ T) z v =
      directionalRankOne f (T z) (fderiv ℂ T z v) := by
  have hreal (w : ComplexVector n) : fderiv ℝ T z w = fderiv ℂ T z w := by
    exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector m => L w)
      (hT.fderiv_restrictScalars ℝ)
  simp only [directionalRankOne, fderiv_comp z hf (hT.restrictScalars ℝ),
    ContinuousLinearMap.comp_apply, hreal, map_smul]

variable {n : ℕ} {M : ComplexManifold n}

theorem leviDirection_congr_of_eventuallyEq
    {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (heq : f =ᶠ[𝓝 z] g) (hf : ContDiffAt ℝ 2 f z) (hg : ContDiffAt ℝ 2 g z)
    (v : ComplexVector n) : leviDirection (leviC f z) v = leviDirection (leviC g z) v := by
  rw [leviDirection, leviC_quadratic_re hf, leviDirection, leviC_quadratic_re hg]
  unfold complexLeviQuadratic
  rw [(heq.fderiv (𝕜 := ℝ)).fderiv_eq (𝕜 := ℝ)]

theorem directionalRankOne_congr_of_eventuallyEq
    {f g : ComplexVector n → ℝ} {z : ComplexVector n}
    (heq : f =ᶠ[𝓝 z] g) (v : ComplexVector n) :
    directionalRankOne f z v = directionalRankOne g z v := by
  simp only [directionalRankOne, heq.fderiv_eq (𝕜 := ℝ)]

theorem metricLeviDirection_chartChange (h : HermitianField M) (a b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hb : chartInv a z ∈ (extChartAt (ComplexModel n) b).source) (v : ComplexVector n) :
    leviDirection (hMat h a z) v =
      leviDirection (hMat h b (realChartChange a b z))
        (fderiv ℂ (realChartChange a b) z v) := by
  have hT := (L12Aux.chartTransition_contDiffAt a b hz hb).differentiableAt (by simp)
  have hreal (w : ComplexVector n) : fderiv ℝ (realChartChange a b) z w =
      fderiv ℂ (realChartChange a b) z w := by
    exact congrArg (fun L : ComplexVector n →L[ℝ] ComplexVector n => L w)
      (hT.fderiv_restrictScalars ℝ)
  have ht : realChartChange a b z ∈ chartTarget b :=
    (extChartAt (ComplexModel n) b).map_source hb
  have H := realMetricInChart_pullback h a b hz hb v v
  change realMetricInChart h a z v v =
    realMetricInChart h b (realChartChange a b z)
      (fderiv ℝ (realChartChange a b) z v) (fderiv ℝ (realChartChange a b) z v) at H
  rw [realMetricInChart_eq_twice_leviDirection h a hz,
    realMetricInChart_eq_twice_leviDirection h b ht, hreal] at H
  linarith

/-- A genuine C² germ in one chart is a genuine C² germ in any overlapping
original holomorphic chart. -/
theorem inChart_contDiffAt_of_overlap (S : M.Carrier → ℝ) (a b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hb : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (hS : ContDiffAt ℝ 2 (inChart b S) (realChartChange a b z)) :
    ContDiffAt ℝ 2 (inChart a S) z ∧
      inChart a S =ᶠ[𝓝 z] ((inChart b S) ∘ realChartChange a b) := by
  have hi : ContinuousAt (chartInv a) z := continuousAt_extChartAt_symm'' hz
  have hs : ∀ᶠ t in 𝓝 z, chartInv a t ∈ (extChartAt (ComplexModel n) b).source :=
    hi.preimage_mem_nhds ((isOpen_extChartAt_source (I := ComplexModel n) b).mem_nhds hb)
  have heq : inChart a S =ᶠ[𝓝 z] ((inChart b S) ∘ realChartChange a b) := by
    filter_upwards [hs] with t ht
    exact congrArg S ((extChartAt (ComplexModel n) b).left_inv ht).symm
  refine ⟨?_,heq⟩
  have hT : ContDiffAt ℝ 2 (realChartChange a b) z :=
    ((L12Aux.chartTransition_contDiffAt a b hz hb).restrict_scalars ℝ).of_le (by simp)
  exact (hS.comp z hT).congr_of_eventuallyEq heq

/-- Both quantitative germ bounds are invariant under the actual
holomorphic coordinate change, so a centered support controls every chart. -/
theorem inChart_directional_bounds_transport
    (h : HermitianField M) (S : M.Carrier → ℝ) (a b : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget a)
    (hb : chartInv a z ∈ (extChartAt (ComplexModel n) b).source)
    (hS : ContDiffAt ℝ 2 (inChart b S) (realChartChange a b z)) (B D : ℝ)
    (hLevi : ∀ w : ComplexVector n,
      leviDirection (leviC (inChart b S) (realChartChange a b z)) w ≤
        B * leviDirection (hMat h b (realChartChange a b z)) w)
    (hRank : ∀ w : ComplexVector n,
      directionalRankOne (inChart b S) (realChartChange a b z) w ≤
        D * leviDirection (hMat h b (realChartChange a b z)) w) :
    ContDiffAt ℝ 2 (inChart a S) z ∧
      (∀ v : ComplexVector n, leviDirection (leviC (inChart a S) z) v ≤
        B * leviDirection (hMat h a z) v) ∧
      (∀ v : ComplexVector n, directionalRankOne (inChart a S) z v ≤
        D * leviDirection (hMat h a z) v) := by
  obtain ⟨hSa,heq⟩ := inChart_contDiffAt_of_overlap S a b hz hb hS
  have hT : ContDiffAt ℂ 2 (realChartChange a b) z :=
    (L12Aux.chartTransition_contDiffAt a b hz hb).of_le (by simp)
  have hcomp : ContDiffAt ℝ 2 ((inChart b S) ∘ realChartChange a b) z :=
    hS.comp z (hT.restrict_scalars ℝ)
  refine ⟨hSa,?_,?_⟩
  · intro v
    rw [leviDirection_congr_of_eventuallyEq heq hSa hcomp v,
      leviDirection_comp_holomorphic hT hS,
      metricLeviDirection_chartChange h a b hz hb]
    exact hLevi _
  · intro v
    rw [directionalRankOne_congr_of_eventuallyEq heq v,
      directionalRankOne_comp_holomorphic (hT.differentiableAt (by norm_num))
        (hS.differentiableAt (by norm_num)),
      metricLeviDirection_chartChange h a b hz hb]
    exact hRank _

end Yau.NodeProofs.P07DistanceLevi
