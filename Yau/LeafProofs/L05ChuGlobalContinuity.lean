import Yau.LeafProofs.L05ChuGlobalOperator

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem holderWeight_tendsto_zero {n : ℕ} {beta : ℝ} (hb : 0 < beta) (p : Point n) :
    Tendsto (fun q : Point n => holderWeight beta q p) (𝓝 p) (𝓝 0) := by
  have hx : Tendsto (fun q : Point n => ‖q.1-p.1‖) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun q : Point n => ‖q.1-p.1‖) := (continuous_fst.sub continuous_const).norm
    simpa only [sub_self,norm_zero] using hc.tendsto p
  have ht : Tendsto (fun q : Point n => |q.2-p.2|) (𝓝 p) (𝓝 0) := by
    have hc : Continuous (fun q : Point n => |q.2-p.2|) := (continuous_snd.sub continuous_const).abs
    simpa only [sub_self,abs_zero] using hc.tendsto p
  have hh := (hx.rpow_const (Or.inr hb.le)).add (ht.rpow_const (Or.inr (by linarith : 0 ≤ beta/2)))
  simpa only [holderWeight,Real.zero_rpow hb.ne',Real.zero_rpow (show beta/2 ≠ 0 by linarith),zero_add] using hh

set_option maxHeartbeats 1400000 in
theorem chuGlobalOperator_continuousOn {n : ℕ} {E U : Set (Sym n)}
    (hEc : IsCompact E) (hne : E.Nonempty)
    {F : Sym n → Point n → ℝ} {S : Point n → Sym n} {T : Sym n → Point n → Sym n}
    {ell L K beta : ℝ} (hell : 0 ≤ ell) (hL : ell ≤ L) (hK : 0 ≤ K) (hb : 0 < beta)
    (hF : ChuH1 E U F ell L K beta) (hT : ChuH2 T K beta) (hS : ChuH3 S K beta) :
    ContinuousOn (fun z : Sym n × Point n => chuGlobalOperator E F S T ell L z.1 z.2)
      (Set.univ ×ˢ backward 1) := by
  intro z hz
  rcases z with ⟨H,p⟩
  have hN : Tendsto (fun w : Sym n × Point n => ‖w.1-H‖) (𝓝 (H,p)) (𝓝 0) := by
    have hc : Continuous (fun w : Sym n × Point n => ‖w.1-H‖) := (continuous_fst.sub continuous_const).norm
    simpa only [sub_self,norm_zero] using hc.tendsto (H,p)
  have hW := (holderWeight_tendsto_zero hb p).comp (continuous_snd.tendsto (H,p))
  have hBound : Tendsto (fun w : Sym n × Point n =>
      (bellmanMatrixConstant n L*chuTransformNormConstant n K)*‖w.1-H‖+
        (chuGlobalTimeConstant n L K*(1+‖H‖))*holderWeight beta w.2 p) (𝓝 (H,p)) (𝓝 0) := by
    convert! (hN.const_mul (bellmanMatrixConstant n L*chuTransformNormConstant n K)).add
      (hW.const_mul (chuGlobalTimeConstant n L K*(1+‖H‖))) using 1 <;> simp only [mul_zero,zero_add] <;> rfl
  change Tendsto (fun w : Sym n × Point n => chuGlobalOperator E F S T ell L w.1 w.2)
    (𝓝[Set.univ ×ˢ backward 1] (H,p)) (𝓝 (chuGlobalOperator E F S T ell L H p))
  apply tendsto_iff_dist_tendsto_zero.mpr
  change Tendsto (fun w : Sym n × Point n =>
    |chuGlobalOperator E F S T ell L w.1 w.2-chuGlobalOperator E F S T ell L H p|)
      (𝓝[Set.univ ×ˢ backward 1] (H,p)) (𝓝 0)
  apply squeeze_zero' (Eventually.of_forall (fun _ => abs_nonneg _)) _
    (hBound.mono_left nhdsWithin_le_nhds)
  filter_upwards [self_mem_nhdsWithin] with w hw
  have hM := chuGlobalOperator_matrix_sub_le (S := S) hEc hne hell hL hK hF hT hw.2 w.1 H
  have hP := chuGlobalOperator_time_holder hEc hne hell hL hK hF hT hS H hw.2 hz.2
  have htri := abs_sub_le (chuGlobalOperator E F S T ell L w.1 w.2)
    (chuGlobalOperator E F S T ell L H w.2) (chuGlobalOperator E F S T ell L H p)
  linarith only [hM,hP,htri]

theorem backward_one_origin_mem (n : ℕ) : ((0,0) : Point n) ∈ backward 1 := by
  refine ⟨Metric.mem_ball_self (by norm_num),?_⟩
  norm_num

theorem holderWeight_backward_origin_le_two {n : ℕ} {beta : ℝ} (hb : 0 ≤ beta)
    {p : Point n} (hp : p ∈ backward 1) : holderWeight beta p (0,0) ≤ 2 := by
  have hxlt : ‖p.1‖ < 1 := by simpa only [Metric.mem_ball,dist_zero_right] using hp.1
  have hx := hxlt.le
  have ht : |p.2| ≤ 1 := abs_le.mpr ⟨by linarith only [hp.2.1],hp.2.2.trans (by norm_num)⟩
  have hs := Real.rpow_le_one (norm_nonneg p.1) hx hb
  have hr := Real.rpow_le_one (abs_nonneg p.2) ht (show 0 ≤ beta/2 by positivity)
  simp only [holderWeight,sub_zero]
  linarith only [hs,hr]

theorem chu_background_norm_le {n : ℕ} {S : Point n → Sym n} {K beta : ℝ}
    (hK : 0 ≤ K) (hb : 0 ≤ beta) (hS : ChuH3 S K beta) {p : Point n} (hp : p ∈ backward 1) :
    ‖S p‖ ≤ 3*K := by
  have hh := hS.2 p hp (0,0) (backward_one_origin_mem n)
  have hw := mul_le_mul_of_nonneg_left (holderWeight_backward_origin_le_two hb hp) hK
  have hn : ‖S p‖ ≤ ‖S p-S (0,0)‖+‖S (0,0)‖ := by
    have he : S p=(S p-S (0,0))+S (0,0) := by abel
    calc
      _=‖(S p-S (0,0))+S (0,0)‖ := congrArg norm he
      _≤_ := norm_add_le _ _
  linarith only [hh,hw,hn,hS.1]

end Yau.LeafProofs.L05Aux
