import Mathlib.Analysis.Calculus.MeanValue

/-! Joint differentiation from actual spatial derivatives continuous in
both variables and an actual derivative in the second variable. The
spatial remainder is controlled by the mean value inequality on a ball. -/

open Set Filter Asymptotics
open scoped Topology
noncomputable section
namespace Yau.Proofs.F05Aux
variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem F05_product_derivative_of_partial {F : E × ℝ → V}
    {A : E × ℝ → E →L[ℝ] V} {p : E × ℝ} {J : V}
    (hSpatial : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun x => F (x,q.2)) (A q) q.1)
    (hA : ContinuousAt A p) (hTime : HasDerivAt (fun t => F (p.1,t)) J p.2) :
    HasFDerivAt F ((A p).comp (ContinuousLinearMap.fst ℝ E ℝ)+
      ((1 : ℝ →L[ℝ] ℝ).smulRight J).comp (ContinuousLinearMap.snd ℝ E ℝ)) p := by
  let G : E × ℝ → V := fun q => A p (q.1-p.1)+F (p.1,q.2)
  have hLinear : HasFDerivAt (fun q : E × ℝ => A p (q.1-p.1))
      ((A p).comp (ContinuousLinearMap.fst ℝ E ℝ)) p :=
    (A p).hasFDerivAt.comp p (hasFDerivAt_fst.sub_const p.1)
  have hTemporal : HasFDerivAt (fun q : E × ℝ => F (p.1,q.2))
      (((1 : ℝ →L[ℝ] ℝ).smulRight J).comp (ContinuousLinearMap.snd ℝ E ℝ)) p :=
    hTime.hasFDerivAt.comp p hasFDerivAt_snd
  let D : (E × ℝ) →L[ℝ] V := (A p).comp (ContinuousLinearMap.fst ℝ E ℝ)+
    ((1 : ℝ →L[ℝ] ℝ).smulRight J).comp (ContinuousLinearMap.snd ℝ E ℝ)
  have hG : HasFDerivAt G D p := hLinear.add hTemporal
  have hSmall : (fun q => F q-G q) =o[𝓝 p] (fun q => q-p) := by
    rw [isLittleO_iff]
    intro ε hε
    have hNear : ∀ᶠ q in 𝓝 p,
        HasFDerivAt (fun x => F (x,q.2)) (A q) q.1 ∧ ‖A q-A p‖ ≤ ε := by
      filter_upwards [hSpatial,hA (Metric.ball_mem_nhds (A p) hε)] with q hq hAq
      have hNorm : ‖A q-A p‖ < ε := by simpa only [Set.mem_preimage,Metric.mem_ball,dist_eq_norm] using hAq
      exact ⟨hq,hNorm.le⟩
    obtain ⟨δ,hδ,hBall⟩ := Metric.eventually_nhds_iff_ball.mp hNear
    filter_upwards [Metric.ball_mem_nhds p hδ] with q hq
    have hQ : q.1 ∈ Metric.ball p.1 δ ∧ q.2 ∈ Metric.ball p.2 δ := by
      simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using hq
    have hPair (x : E) (hx : x ∈ Metric.ball p.1 δ) : (x,q.2) ∈ Metric.ball p δ := by
      simpa only [Metric.mem_ball,Prod.dist_eq,max_lt_iff] using (show x ∈ Metric.ball p.1 δ ∧ q.2 ∈ Metric.ball p.2 δ from ⟨hx,hQ.2⟩)
    have hMVT := (convex_ball p.1 δ).norm_image_sub_le_of_norm_hasFDerivWithin_le'
      (f := fun x : E => F (x,q.2)) (f' := fun x => A (x,q.2)) (φ := A p) (fun x hx => (hBall (x,q.2) (hPair x hx)).1.hasFDerivWithinAt)
      (fun x hx => (hBall (x,q.2) (hPair x hx)).2) (Metric.mem_ball_self hδ) hQ.1
    calc
      ‖F q-G q‖ = ‖F (q.1,q.2)-F (p.1,q.2)-A p (q.1-p.1)‖ := by
        dsimp only [G]
        congr 1
        abel
      _ ≤ ε*‖q.1-p.1‖ := hMVT
      _ ≤ ε*‖q-p‖ := mul_le_mul_of_nonneg_left (norm_fst_le (q-p)) hε.le
  have hAt : F p = G p := by simp only [G,sub_self,map_zero,zero_add,Prod.eta]
  apply HasFDerivAt.of_isLittleO
  have hSum := hSmall.add hG.isLittleO
  convert hSum using 1
  funext q
  rw [hAt]
  abel

end Yau.Proofs.F05Aux
