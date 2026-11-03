import Yau.Proofs.C05RelativeTraceBound
import Yau.Proofs.C05HarnackSourceJetBounds
import Yau.Proofs.C05ScalarGradientNorm

/-! On the same original normalized good sequence, the actual gradient
at the center tends to zero directly from scalar Harnack and the scalar trace. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix ComplexOrder
namespace Yau.Proofs.C05Aux
open Yau Blueprint C04Aux C04RescaledTubeAux Set Filter Yau.LeafProofs
variable {n : ℕ} {X : KahlerManifold n}
set_option backward.isDefEq.respectTransparency false

theorem normalized_scalarGradient_sq_le_defect (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (x : Pt X) (t R : ℝ) (ht : 0 < t) (hR : 0 < R)
    (hnorm : scalarCurvature (scaleField R hR (h t)) x = 1) :
    scalarJetNorm (scaleField R hR (h t)) (scalarCurvature (scaleField R hR (h t))) 1 x ^ 2 ≤
      2 * (scalarHarnackSum h x t / R ^ 2) := by
  let k := scaleField R hR (h t)
  have hbase := L23Aux.metricFamilySmooth_slice h hf.1.2.1 (show t ∈ Ici (0:ℝ) from ht.le)
  have hk : MetricSmooth k := metricSmooth_scale R hR (h t) hbase
  have hs : SmoothFn (scalarCurvature (h t)) :=
    spaceSlice_smoothFn (localizedFlow_scalar_smoothSpaceTime X o h U P ρ hf) ht
  have hgp : (gMat k x).PosDef := L18Aux.hMat_posDef k x (chartPt x x) (mem_extChartAt_target x)
  have htr : ((gMat k x)⁻¹ * ricci (h t) x).trace.re = 1 := by
    change traceWith (gMat k x) (ricci (h t) x) = 1
    rw [← ricci_scaleField R hR (h t) x]
    exact hnorm
  have hquad : ∀ v : Fin n → ℂ, 0 ≤ scalarHarnackSum h x t +
      2 * (∑ i, v i * scalarCovector (h t) x i).re +
        (star v ⬝ᵥ (ricci (h t) x *ᵥ v)).re := by
    intro v
    simpa only [scalarHarnackSum,scalarCovector,WithLp.ofLp_toLp] using
      hH.2.2.2.2.1 x t ht (WithLp.toLp 2 v)
  have hQ := metric_dual_le_harnack_of_trace_one (gMat k x) (ricci (h t) x) hgp
    (hH.2.2.1 t ht.le x) htr (scalarCovector (h t) x) (scalarHarnackSum h x t) hquad
  change gradNormSq k (scalarCurvature (h t)) x ≤ scalarHarnackSum h x t at hQ
  have hN := scalarJetNorm_one_sq_eq_twice_gradNormSq k (scalarCurvature (h t)) hs x
  have hNbound : scalarJetNorm k (scalarCurvature (h t)) 1 x ^ 2 ≤
      2 * scalarHarnackSum h x t := by linarith
  have hsc : scalarCurvature k = (fun y => R⁻¹ * scalarCurvature (h t) y) := by
    funext y
    exact scalar_scaleField R hR (h t) y
  change scalarJetNorm k (scalarCurvature k) 1 x ^ 2 ≤ _
  rw [hsc,scalarJetNorm_const_mul k hk _ hs,abs_of_pos (inv_pos.mpr hR),mul_pow]
  have hh := mul_le_mul_of_nonneg_left hNbound (sq_nonneg R⁻¹)
  convert hh using 1 <;> field_simp [hR.ne'] <;> ring

theorem normalized_center_gradient_tendsto_zero (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hf : LocalizedFlow X o h U P ρ) (hH : HarnackCompleteness X o h)
    (tw : ℕ → ℝ) (htw : ∀ i, 0 < tw i)
    (hRi : ∀ i, 0 < scalarCurvature (h (tw i)) o)
    (hdefect : Tendsto (fun i => scalarHarnackSum h o (tw i) /
      scalarCurvature (h (tw i)) o ^ 2) atTop (𝓝 0)) :
    Tendsto (fun i =>
      let k := scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))
      scalarJetNorm k (scalarCurvature k) 1 o) atTop (𝓝 0) := by
  let N : ℕ → ℝ := fun i =>
    let k := scaleField (scalarCurvature (h (tw i)) o) (hRi i) (h (tw i))
    scalarJetNorm k (scalarCurvature k) 1 o
  have hN (i : ℕ) : 0 ≤ N i := scalarJetNorm_nonneg _ _ _ _
  have hs : Tendsto (fun i => N i ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero (fun i => sq_nonneg (N i))
      (fun i => normalized_scalarGradient_sq_le_defect o h U P ρ hf hH o (tw i)
        (scalarCurvature (h (tw i)) o) (htw i) (hRi i) (scalar_normalized (h (tw i)) o (hRi i)))
    simpa only [mul_zero] using hdefect.const_mul 2
  have ht := Real.continuous_sqrt.continuousAt.tendsto.comp hs
  change Tendsto N atTop (𝓝 0)
  simpa only [Function.comp_def,Real.sqrt_sq (hN _),Real.sqrt_zero] using ht

end Yau.Proofs.C05Aux
