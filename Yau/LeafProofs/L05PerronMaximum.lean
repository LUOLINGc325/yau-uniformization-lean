import Yau.LeafProofs.L05PerronClassical

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perronTimePenalty {n : ℕ} (m eta b : ℝ) (p : Point n) : ℝ := m+eta/(b-p.2)

theorem perron_timeOnly_hessian {n : ℕ} (f : ℝ → ℝ) (p : Point n) :
    hessian (fun q : Point n => f q.2) p=0 := by
  simp [hessian,spatialDD]
  exact (selfAdjointPart ℝ).map_zero

theorem perronTimePenalty_timeD {n : ℕ} (m eta b : ℝ) (p : Point n) (hp : b-p.2≠0) :
    timeD Set.univ (perronTimePenalty m eta b) p=eta/(b-p.2)^2 := by
  have hd : HasDerivAt (fun t : ℝ => m+eta/(b-t)) (eta/(b-p.2)^2) p.2 := by
    convert! ((hasDerivAt_const p.2 eta).div
      ((hasDerivAt_const p.2 b).sub (hasDerivAt_id p.2)) hp).const_add m using 1 <;>
      simp [Pi.sub_apply,div_eq_mul_inv,inv_pow]
  simpa only [timeD,perronTimePenalty,Set.mem_univ,Set.ofPred_true,derivWithin_univ] using hd.deriv

set_option maxHeartbeats 1000000 in
theorem perron_pucci_maximum {n : ℕ} {ell L R a b : ℝ}
    (hell : 0≤ell) (hL : ell≤L) (hR : 0<R) (hab : a<b) {w : Point n → ℝ}
    (hw : ContinuousOn w (abpClosed n R a b))
    (hsub : viscositySub (abpOpen n R a b) (fun H _ => pucciPlus ell L H) (fun _ => 0) w)
    (hbd : ∀ p∈abpBoundary n R a b, w p≤0) : ∀ p∈abpClosed n R a b, w p≤0 := by
  have hD : IsCompact (abpClosed n R a b) := (isCompact_closedBall (0 : Space n) R).prod isCompact_Icc
  obtain ⟨C,hC⟩ := hD.bddAbove_image hw
  let M := |C|+1
  have hM : 0<M := by dsimp only [M]; positivity
  have hwM (p : Point n) (hp : p∈abpClosed n R a b) : w p≤M := by
    have hh := hC (Set.mem_image_of_mem w hp)
    dsimp only [M]
    linarith [le_abs_self C]
  have hbefore (p : Point n) (hp : p∈abpClosed n R a b) (hpb : p.2<b) : w p≤0 := by
    by_contra hpos
    have hwp : 0<w p := lt_of_not_ge hpos
    let eta := w p*(b-p.2)/2
    have heta : 0<eta := by dsimp only [eta]; positivity
    have hpval : 0<w p-eta/(b-p.2) := by
      have he : eta/(b-p.2)=w p/2 := by dsimp only [eta]; field_simp
      rw [he]
      linarith
    let delta := min ((b-p.2)/2) (eta/(2*M))
    have hd : 0<delta := by dsimp only [delta]; positivity
    let T := b-delta
    have hpT : p.2<T := by
      have hh : delta≤(b-p.2)/2 := min_le_left _ _
      dsimp only [T]
      linarith
    have hTb : T<b := by dsimp only [T]; linarith
    have haT : a<T := hp.2.1.trans_lt hpT
    have hpenT : 2*M≤eta/(b-T) := by
      have hh : delta≤eta/(2*M) := min_le_right _ _
      have hh' := (le_div_iff₀ (by positivity : 0<2*M)).mp hh
      apply (le_div_iff₀ (sub_pos.mpr hTb)).mpr
      dsimp only [T]
      nlinarith
    let K := abpClosed n R a T
    let cost := fun q : Point n => w q-eta/(b-q.2)
    have hK : IsCompact K := (isCompact_closedBall (0 : Space n) R).prod isCompact_Icc
    have hpK : p∈K := ⟨hp.1,hp.2.1,hpT.le⟩
    have hKD : K⊆abpClosed n R a b := fun q hq => ⟨hq.1,hq.2.1,hq.2.2.trans hTb.le⟩
    have hc : ContinuousOn cost K := by
      exact (hw.mono hKD).sub (continuousOn_const.div (continuousOn_const.sub continuous_snd.continuousOn)
        (fun q hq => ne_of_gt (sub_pos.mpr (hq.2.2.trans_lt hTb))))
    obtain ⟨z,hz,hmax⟩ := hc.upperSemicontinuousOn.exists_isMaxOn ⟨p,hpK⟩ hK
    have hm : 0<cost z := hpval.trans_le (hmax hpK)
    have hden : 0<b-z.2 := sub_pos.mpr (hz.2.2.trans_lt hTb)
    have hpen : 0<eta/(b-z.2) := div_pos heta hden
    have hzR : z.1∈Metric.ball (0 : Space n) R := by
      have hle : ‖z.1‖≤R := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
      by_contra hfail
      have hnot : ¬‖z.1‖<R := by simpa only [Metric.mem_ball,dist_zero_right] using hfail
      have heq : ‖z.1‖=R := le_antisymm hle (le_of_not_gt hnot)
      have hbz := hbd z (Or.inr ⟨by simpa only [Metric.mem_sphere,dist_zero_right] using heq,
        hz.2.1,hz.2.2.trans hTb.le⟩)
      dsimp only [cost] at hm
      linarith
    have hza : a<z.2 := by
      by_contra hfail
      have heq : z.2=a := le_antisymm (le_of_not_gt hfail) hz.2.1
      have hbz := hbd z (Or.inl ⟨hz.1,heq⟩)
      dsimp only [cost] at hm
      linarith
    have hzT : z.2<T := by
      by_contra hfail
      have heq : z.2=T := le_antisymm hz.2.2 (le_of_not_gt hfail)
      have hbound := hwM z (hKD hz)
      dsimp only [cost] at hm
      rw [heq] at hm
      linarith
    let phi : Point n → ℝ := perronTimePenalty (cost z) eta b
    have hphi : ContDiffAt ℝ 2 phi z := by
      dsimp only [phi,perronTimePenalty]
      exact contDiffAt_const.add (contDiffAt_const.div (by fun_prop) (ne_of_gt hden))
    have ht : touchAbove phi w z := by
      refine ⟨?_,?_⟩
      · dsimp only [phi,perronTimePenalty,cost]
        ring
      · have hnear : abpOpen n R a T∈𝓝 z :=
          (Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds ⟨hzR,hza,hzT⟩
        filter_upwards [hnear] with q hq
        have hh := hmax (show q∈K from ⟨Metric.ball_subset_closedBall hq.1,hq.2.1.le,hq.2.2.le⟩)
        change w q-eta/(b-q.2)≤cost z at hh
        exact (sub_le_iff_le_add).mp hh
    have hi := hsub z ⟨hzR,hza,hzT.trans hTb⟩ phi hphi ht
    have hH : hessian phi z=0 := by
      change hessian (fun r : Point n => cost z+eta/(b-r.2)) z=0
      exact perron_timeOnly_hessian (fun t : ℝ => cost z+eta/(b-t)) z
    have htime : timeD Set.univ phi z=eta/(b-z.2)^2 :=
      perronTimePenalty_timeD (cost z) eta b z hden.ne'
    change timeD Set.univ phi z-pucciPlus ell L (hessian phi z)≤0 at hi
    rw [hH,pucciPlus_zero hell hL,htime,sub_zero] at hi
    exact (not_le.mpr (div_pos heta (sq_pos_of_ne_zero hden.ne'))) hi
  intro p hp
  by_cases hpb : p.2<b
  · exact hbefore p hp hpb
  · have hpt : p.2=b := le_antisymm hp.2.2 (le_of_not_gt hpb)
    let r : ℕ → ℝ := fun j => ((b-a)/2)*(1/((j:ℝ)+1))
    have hr (j : ℕ) : 0<r j := by dsimp only [r]; positivity
    have hr1 (j : ℕ) : r j≤(b-a)/2 := by
      have hh : (1:ℝ)/((j:ℝ)+1)≤1 := by
        apply (div_le_iff₀ (by positivity : (0:ℝ)<(j:ℝ)+1)).mpr
        norm_num
      dsimp only [r]
      nlinarith
    have hr0 : Tendsto r atTop (𝓝 0) := by
      simpa only [r,mul_zero] using
        (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul ((b-a)/2)
    let q : ℕ → Point n := fun j => (p.1,b-r j)
    have hq (j : ℕ) : q j∈abpClosed n R a b :=
      ⟨hp.1,by dsimp only [q]; linarith [hr1 j],by dsimp only [q]; linarith [hr j]⟩
    have hqb (j : ℕ) : (q j).2<b := by dsimp only [q]; linarith [hr j]
    have hqt : Tendsto q atTop (𝓝 p) := by
      have ht := (tendsto_const_nhds (x := b)).sub hr0
      have hh := (tendsto_const_nhds (x := p.1)).prodMk_nhds ht
      simpa only [q,sub_zero,←hpt,Prod.eta] using hh
    have hqtD : Tendsto q atTop (𝓝[abpClosed n R a b] p) :=
      tendsto_nhdsWithin_iff.mpr ⟨hqt,Filter.Eventually.of_forall hq⟩
    exact le_of_tendsto ((hw p hp).tendsto.comp hqtD)
      (Filter.Eventually.of_forall (fun j => hbefore (q j) (hq j) (hqb j)))

end Yau.LeafProofs.L05Aux
