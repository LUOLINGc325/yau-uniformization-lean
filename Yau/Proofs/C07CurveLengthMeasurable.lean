import Yau.LeafProofs.L23FieldMetric

open scoped Manifold Topology ContDiff

noncomputable section

namespace Yau.Proofs.C07CurveLengthAux

open Yau Set Filter MeasureTheory
open Yau.LeafProofs

variable {n : ℕ} {M : ComplexManifold n}

/-- The original piecewise-C¹ condition gives actual real manifold
regularity at every interior point outside the finite corner set. -/
theorem piecewise_contMDiffAt {x y : M.Carrier} (γ : PiecewiseC1Curve x y)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hb : t ∉ γ.breakpoints) :
    letI := L12Aux.manifold_realSmooth M
    ContMDiffAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 γ.toFun t := by
  letI := L12Aux.manifold_realSmooth M
  rw [contMDiffAt_iff]
  refine ⟨γ.continuous_on.continuousAt (Icc_mem_nhds ht.1 ht.2), ?_⟩
  convert! (γ.piecewise_c1 t hb).contDiffWithinAt using 1

/-- Smoothness of the actual metric makes the speed continuous away from
the finitely many corners of the original curve. -/
theorem curveSpeed_continuousAt (k : HermitianField M) (hk : MetricSmooth k)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y)
    {t : ℝ} (ht : t ∈ Ioo (0 : ℝ) 1) (hb : t ∉ γ.breakpoints) :
    ContinuousAt (curveSpeed k γ) t := by
  letI := L12Aux.manifold_realSmooth M
  letI : ∀ u : M.Carrier, NormedAddCommGroup (TangentSpace 𝓘(ℝ, ComplexVector n) u) :=
    fun u => L12Aux.underlyingRealTangentNormedAddCommGroup k u
  letI : ∀ u : M.Carrier, InnerProductSpace ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) u) :=
    fun u => L12Aux.underlyingRealTangentInnerProductSpace k u
  letI := L23Aux.realRiemannianBundle_continuous k hk
  have hγ := piecewise_contMDiffAt γ ht hb
  have hv : ContinuousAt (fun s : ℝ =>
      (⟨γ s, L12Aux.realCurveVelocity γ s⟩ : TangentBundle 𝓘(ℝ, ComplexVector n) M.Carrier)) t := by
    let V : ℝ → TangentBundle 𝓘(ℝ, ℝ) ℝ := fun s =>
      ⟨s, (tangentSpaceCastModel 𝓘(ℝ, ℝ) s).symm 1⟩
    have hV : ContinuousAt V t := L12Aux.continuous_realLineUnitSection.continuousAt
    have hTM : ContinuousAt (tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ.toFun) (V t) :=
      hγ.continuousAt_tangentMap (x₀ := V t) (by norm_num)
    have hcomp : ContinuousAt ((tangentMap 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) γ.toFun) ∘ V) t :=
      hTM.comp hV
    convert! hcomp using 1
  have hi := hv.inner_bundle hv
  have hs := Real.continuous_sqrt.continuousAt.comp hi
  have hn : ContinuousAt (fun s : ℝ => ‖L12Aux.realCurveVelocity γ s‖) t := by
    convert! hs using 1
  have heq : curveSpeed k γ =ᶠ[𝓝 t] (fun s => ‖L12Aux.realCurveVelocity γ s‖) := by
    have hnb : (γ.breakpoints : Set ℝ)ᶜ ∈ 𝓝 t :=
      γ.breakpoints.finite_toSet.isClosed.isOpen_compl.mem_nhds hb
    filter_upwards [Ioo_mem_nhds ht.1 ht.2, hnb] with s hs hbs
    exact (L12Aux.realCurveVelocity_norm k γ hs hbs).symm
  exact hn.congr_of_eventuallyEq heq

theorem curveSpeed_continuousOn (k : HermitianField M) (hk : MetricSmooth k)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) :
    ContinuousOn (curveSpeed k γ) (Ioo (0 : ℝ) 1 \ (γ.breakpoints : Set ℝ)) := by
  intro t ht
  exact (curveSpeed_continuousAt k hk γ ht.1 ht.2).continuousWithinAt

/-- No measurability certificate is supplied by the caller: it follows
from the smooth metric and the original finite-corner curve definition. -/
theorem curveSpeed_aestronglyMeasurable (k : HermitianField M) (hk : MetricSmooth k)
    {x y : M.Carrier} (γ : PiecewiseC1Curve x y) :
    AEStronglyMeasurable (curveSpeed k γ) (volume.restrict (Icc (0 : ℝ) 1)) := by
  let S := Ioo (0 : ℝ) 1 \ (γ.breakpoints : Set ℝ)
  have hS : MeasurableSet S := measurableSet_Ioo.diff γ.breakpoints.finite_toSet.measurableSet
  have hm := (curveSpeed_continuousOn k hk γ).aestronglyMeasurable (μ := volume) hS
  have hdiff : S =ᵐ[volume] Ioo (0 : ℝ) 1 := by
    filter_upwards [γ.breakpoints.finite_toSet.countable.ae_notMem volume] with t ht
    simp only [S, Set.mem_sdiff, ht, not_false_eq_true, and_true]
  have hae := hdiff.trans (Ioo_ae_eq_Icc (μ := volume))
  rw [← Measure.restrict_congr_set hae]
  exact hm

end Yau.Proofs.C07CurveLengthAux
