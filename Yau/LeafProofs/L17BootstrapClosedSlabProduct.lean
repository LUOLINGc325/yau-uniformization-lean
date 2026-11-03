import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Normed.Operator.Bilinear

open Set Filter Metric
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17BootstrapClosedSlabAux

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]

theorem hasFDerivWithinAt_of_spatial_time {O : Set E} (_hO : IsOpen O) (hconv : Convex ℝ O)
    {T : ℝ} (_hT : 0 < T) {f : E × ℝ → F} {A : E × ℝ → E →L[ℝ] F} {b : E × ℝ → F}
    (_hf : ContinuousOn f (O ×ˢ Icc 0 T)) (hA : ContinuousOn A (O ×ˢ Icc 0 T))
    (hb : ContinuousOn b (O ×ˢ Icc 0 T))
    (hspace : ∀ z∈O, ∀ t∈Icc 0 T, HasFDerivAt (fun y : E => f (y,t)) (A (z,t)) z)
    (htime : ∀ z∈O, ∀ t∈Icc 0 T, HasDerivWithinAt (fun s : ℝ => f (z,s)) (b (z,t)) (Icc 0 T) t)
    {z : E} {t : ℝ} (hz : z∈O) (ht : t∈Icc 0 T) :
    HasFDerivWithinAt f
      ((A (z,t)).comp (ContinuousLinearMap.fst ℝ E ℝ)+
        (ContinuousLinearMap.snd ℝ E ℝ).smulRight (b (z,t))) (O ×ˢ Icc 0 T) (z,t) := by
  rw [hasFDerivWithinAt_iff_isLittleO]
  apply Asymptotics.IsLittleO.of_bound
  intro eps heps
  obtain ⟨dA,hdA,hnearA⟩ := Metric.continuousWithinAt_iff.mp (hA (z,t) ⟨hz,ht⟩) (eps/2) (half_pos heps)
  obtain ⟨db,hdb,hnearb⟩ := Metric.continuousWithinAt_iff.mp (hb (z,t) ⟨hz,ht⟩) (eps/2) (half_pos heps)
  let d := min dA db
  have hd : 0 < d := lt_min hdA hdb
  have hNear : ball (z,t) d∈𝓝[O ×ˢ Icc 0 T] (z,t) :=
    mem_nhdsWithin_of_mem_nhds (ball_mem_nhds _ hd)
  filter_upwards [self_mem_nhdsWithin,hNear] with p hp hpd
  have hpdist : dist p (z,t) < d := hpd
  have hxdist : dist p.1 z < d := (max_lt_iff.mp (by simpa only [Prod.dist_eq] using hpdist)).1
  have htdist : dist p.2 t < d := (max_lt_iff.mp (by simpa only [Prod.dist_eq] using hpdist)).2
  let A0 := A (z,t)
  let b0 := b (z,t)
  let V : Set E := O ∩ ball z d
  have hzV : z∈V := ⟨hz,mem_ball_self hd⟩
  have hpV : p.1∈V := ⟨hp.1,hxdist⟩
  have hSA (y : E) (hy : y∈V) : ‖A (y,p.2)-A0‖ ≤ eps/2 := by
    have hDist : dist (y,p.2) (z,t) < dA := by
      rw [Prod.dist_eq]
      exact max_lt ((show dist y z < d from hy.2).trans_le (min_le_left _ _))
        (htdist.trans_le (min_le_left _ _))
    exact le_of_lt (by simpa only [dist_eq_norm,A0] using hnearA (x := (y,p.2)) ⟨hy.1,hp.2⟩ hDist)
  have hSD (y : E) (hy : y∈V) :
      HasFDerivWithinAt (fun w : E => f (w,p.2)-A0 w) (A (y,p.2)-A0) V y := by
    convert! ((hspace y hy.1 p.2 hp.2).sub (A0.hasFDerivAt (x := y))).hasFDerivWithinAt using 1
  have hSM := Convex.norm_image_sub_le_of_norm_hasFDerivWithin_le hSD hSA
    (hconv.inter (convex_ball z d)) hzV hpV
  change ‖(f (p.1,p.2)-A0 p.1)-(f (z,p.2)-A0 z)‖ ≤ (eps/2)*‖p.1-z‖ at hSM
  have hSEq : (f (p.1,p.2)-A0 p.1)-(f (z,p.2)-A0 z)=
      f (p.1,p.2)-f (z,p.2)-A0 (p.1-z) := by rw [map_sub]; abel
  rw [hSEq] at hSM
  let J : Set ℝ := Icc 0 T ∩ ball t d
  have htJ : t∈J := ⟨ht,mem_ball_self hd⟩
  have hpJ : p.2∈J := ⟨hp.2,htdist⟩
  have hTA (s : ℝ) (hs : s∈J) : ‖b (z,s)-b0‖ ≤ eps/2 := by
    have hDist : dist (z,s) (z,t) < db := by
      rw [Prod.dist_eq,dist_self,max_eq_right (dist_nonneg : 0 ≤ dist s t)]
      exact (show dist s t < d from hs.2).trans_le (min_le_right _ _)
    exact le_of_lt (by simpa only [dist_eq_norm,b0] using hnearb (x := (z,s)) ⟨hz,hs.1⟩ hDist)
  have hTD (s : ℝ) (hs : s∈J) :
      HasDerivWithinAt (fun a : ℝ => f (z,a)-a • b0) (b (z,s)-b0) J s := by
    have hLin : HasDerivAt (fun a : ℝ => a • b0) b0 s := by
      simpa only [id_eq,one_smul] using (hasDerivAt_id s).smul_const b0
    convert! ((htime z hz s hs.1).sub hLin.hasDerivWithinAt).mono inter_subset_left using 1
  have hTM := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hTD hTA
    ((convex_Icc (0 : ℝ) T).inter (convex_ball t d)) htJ hpJ
  change ‖(f (z,p.2)-p.2 • b0)-(f (z,t)-t • b0)‖ ≤ (eps/2)*‖p.2-t‖ at hTM
  have hTEq : (f (z,p.2)-p.2 • b0)-(f (z,t)-t • b0)=
      f (z,p.2)-f (z,t)-(p.2-t) • b0 := by rw [sub_smul]; abel
  rw [hTEq] at hTM
  have hEval : ((A (z,t)).comp (ContinuousLinearMap.fst ℝ E ℝ)+
      (ContinuousLinearMap.snd ℝ E ℝ).smulRight (b (z,t))) (p-(z,t))=
      A0 (p.1-z)+(p.2-t) • b0 := rfl
  rw [hEval]
  have hSplit : f p-f (z,t)-(A0 (p.1-z)+(p.2-t) • b0)=
      (f (p.1,p.2)-f (z,p.2)-A0 (p.1-z))+(f (z,p.2)-f (z,t)-(p.2-t) • b0) := by
    change f (p.1,p.2)-f (z,t)-(A0 (p.1-z)+(p.2-t) • b0)=_
    abel
  rw [hSplit]
  calc
    _ ≤ ‖f (p.1,p.2)-f (z,p.2)-A0 (p.1-z)‖+‖f (z,p.2)-f (z,t)-(p.2-t) • b0‖ := norm_add_le _ _
    _ ≤ (eps/2)*‖p.1-z‖+(eps/2)*‖p.2-t‖ := add_le_add hSM hTM
    _ ≤ eps*‖p-(z,t)‖ := by
      have hxN : ‖p.1-z‖ ≤ ‖p-(z,t)‖ := norm_fst_le (p-(z,t))
      have htN : ‖p.2-t‖ ≤ ‖p-(z,t)‖ := norm_snd_le (p-(z,t))
      nlinarith [mul_le_mul_of_nonneg_left hxN (half_pos heps).le,
        mul_le_mul_of_nonneg_left htN (half_pos heps).le]

end Yau.LeafProofs.L17BootstrapClosedSlabAux
