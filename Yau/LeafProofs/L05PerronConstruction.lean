import Yau.LeafProofs.L05PerronClass
import Yau.LeafProofs.L05PerronBump
import Yau.LeafProofs.L05PerronPatch

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

def perronLowerSolution {n : ℕ} (F : Sym n → ℝ) (G : Point n → ℝ) (B : ℝ) : Point n → ℝ :=
  perronLower (perronSlab n) (perronUpperSolution F G B)

set_option maxHeartbeats 1600000 in
theorem perron_lowerSolution_boundary {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hE : globalElliptic F ell L) (h0 : F 0=0)
    {G : Point n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ContinuousOn G (abpClosed n 1 (-1) 1))
    (hbG : ∀ q ∈ abpClosed n 1 (-1) 1, |G q| ≤ B)
    (hne : (perronClass F G B).Nonempty) :
    ∀ p ∈ perronBoundary n, G p ≤ perronLowerSolution F G B p := by
  intro p hp
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨l,h,hl,hh,hlp,hhp,hdom,hlSub,hhSuper⟩ :=
    perron_boundary_barriers hn hell hL hE h0 hB hG hbG hp heps
  let c := fun q : Point n => max (-B) (l q)
  have hc : Continuous c := continuous_const.max hl.continuous
  have hmem : c ∈ perronClass F G B := by
    refine ⟨hc.continuousOn.upperSemicontinuousOn,?_,?_,?_⟩
    · intro q hq
      refine ⟨le_max_left _ _,max_le (by linarith) ?_⟩
      exact (hdom q (perron_slab_subset_closed hq)).1.trans
        (abs_le.mp (hbG q (perron_slab_subset_closed hq))).2
    · intro q hq
      have hqD := perron_slab_subset_closed (perronBoundary_subset_slab hq)
      exact max_le (abs_le.mp (hbG q hqD)).1 (hdom q hqD).1
    · exact viscositySub_max (perron_constant_solution hell hE h0 (perronOpen n) (-B)).1 hlSub
  have hcV := perron_continuous_le_lower (perron_upperSolution_bounds hne)
    hc.continuousOn (perron_class_le_upperSolution hne hmem) (perronBoundary_subset_slab hp)
  have hlc : l p ≤ c p := le_max_right _ _
  rw [hlp] at hlc
  change c p ≤ perronLowerSolution F G B p at hcV
  linarith

set_option maxHeartbeats 1800000 in
theorem perron_lowerSolution_super {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (h0 : F 0=0)
    {G : Point n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ContinuousOn G (abpClosed n 1 (-1) 1))
    (hbG : ∀ q ∈ abpClosed n 1 (-1) 1, |G q| ≤ B)
    (hne : (perronClass F G B).Nonempty) :
    viscositySuper (perronOpen n) (fun H _ => F H) (fun _ => 0) (perronLowerSolution F G B) := by
  let w := perronUpperSolution F G B
  let v := perronLowerSolution F G B
  have hw := perron_upperSolution_member hn hell hL hF hE h0 hB hG hbG hne
  have hwb : ∀ q ∈ perronSlab n, |w q| ≤ B := perron_upperSolution_bounds hne
  have hvw (q : Point n) (hq : q ∈ perronSlab n) : v q ≤ w q :=
    (perron_lower_bounds hwb hq).1
  have hvb (q : Point n) (hq : q ∈ perronOpen n) : v q ≤ B :=
    (abs_le.mp (perron_lower_bounds hwb (perronOpen_subset_slab hq)).2).2
  intro p hp phi hphi ht
  change 0 ≤ timeD Set.univ phi p-F (hessian phi p)
  by_contra hnot
  obtain ⟨r,delta,hr,hd,hK,z,hzc,hzp,hzs,hzb,hann⟩ :=
    perron_failed_lower_test_bump hn hell hL hF hE h0 (perronOpen_isOpen n) hp hvb hphi ht
      (lt_of_not_ge hnot)
  have hcollar (q : Point n) (hqlo : r/2 ≤ dist q p) (hqhi : dist q p ≤ r) : z q ≤ w q :=
    (hann q hqlo hqhi).trans (hvw q (perronOpen_subset_slab (hK (Metric.mem_closedBall.mpr hqhi))))
  have hpatch : perronMaxPatch w z p r ∈ perronClass F G B := by
    refine ⟨perron_patch_usc hr hw.1 hzc hcollar,perron_patch_bounds hw.2.1 hzb,?_,
      perron_patch_sub hr hK hw.2.2.2 hzs hcollar⟩
    intro q hq
    rw [perron_patch_boundary_eq w z hK hq]
    exact hw.2.2.1 q hq
  have hmax := perron_class_le_upperSolution hne hpatch
  obtain ⟨q,hq,hqt,hval⟩ := perron_lower_recovery hwb (perronOpen_subset_slab hp)
  have hzcAt : ContinuousAt z p := (hzc p (Metric.mem_closedBall_self hr.le)).continuousAt
    (Metric.closedBall_mem_nhds p hr)
  have hdiff : Tendsto (fun k => z (q k)-w (q k)) atTop (𝓝 delta) := by
    have htend := (hzcAt.tendsto.comp hqt).sub hval
    have hcenter : z p-perronLower (perronSlab n) w p=delta := by
      change z p-v p=delta
      rw [hzp]
      ring
    convert! htend using 1
    rw [hcenter]
  have hepos : ∀ᶠ k in atTop, 0 < z (q k)-w (q k) := hdiff (eventually_gt_nhds hd)
  have heball : ∀ᶠ k in atTop, q k ∈ Metric.ball p r :=
    hqt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  obtain ⟨k,hkpos,hkball⟩ := (hepos.and heball).exists
  have hle := hmax (q k) (hq k)
  have hzle : z (q k) ≤ perronMaxPatch w z p r (q k) := by
    change z (q k) ≤ if dist (q k) p<r then max (w (q k)) (z (q k)) else w (q k)
    rw [if_pos (Metric.mem_ball.mp hkball)]
    exact le_max_right _ _
  change perronMaxPatch w z p r (q k) ≤ w (q k) at hle
  linarith

set_option maxHeartbeats 1800000 in
theorem perron_construct {n : ℕ} (hn : 0 < n) {ell L : ℝ}
    (hell : 0 < ell) (hL : ell ≤ L) {F : Sym n → ℝ}
    (hF : Continuous F) (hE : globalElliptic F ell L) (h0 : F 0=0)
    {G : Point n → ℝ} {B : ℝ} (hB : 0 ≤ B)
    (hG : ContinuousOn G (abpClosed n 1 (-1) 1))
    (hbG : ∀ q ∈ abpClosed n 1 (-1) 1, |G q| ≤ B) :
    ∃ w : Point n → ℝ, ContinuousOn w (perronSlab n) ∧
      Set.EqOn w G (perronBoundary n) ∧
      viscositySolution (perronOpen n) (fun H _ => F H) (fun _ => 0) w ∧
      ∀ q ∈ perronSlab n, |w q| ≤ B := by
  have hne := perron_class_nonempty hell hE h0 hB (fun q hq => hbG q (perron_slab_subset_closed hq))
  let w := perronUpperSolution F G B
  let v := perronLowerSolution F G B
  have hw := perron_upperSolution_member hn hell hL hF hE h0 hB hG hbG hne
  have hwb : ∀ q ∈ perronSlab n, |w q| ≤ B := perron_upperSolution_bounds hne
  have hvw (q : Point n) (hq : q ∈ perronSlab n) : v q ≤ w q := (perron_lower_bounds hwb hq).1
  have hvl : LowerSemicontinuousOn v (perronSlab n) := perron_lower_lsc hwb
  have hvs := perron_lowerSolution_super hn hell hL hF hE h0 hB hG hbG hne
  have hbd (q : Point n) (hq : q ∈ perronBoundary n) : w q ≤ v q :=
    (hw.2.2.1 q hq).trans (perron_lowerSolution_boundary hn hell hL hE h0 hB hG hbG hne q hq)
  have hwv := perron_semicont_compare hn hell hL hF hE hw.1 hvl
    ⟨B,hB,fun q hq => ⟨hwb q hq,(perron_lower_bounds hwb hq).2⟩⟩ hw.2.2.2 hvs hbd
  have heq : Set.EqOn w v (perronSlab n) := fun q hq => le_antisymm (hwv q hq) (hvw q hq)
  have hwl : LowerSemicontinuousOn w (perronSlab n) := by
    intro p hp a ha
    have hnear := hvl p hp a (by change a < v p; rw [← heq hp]; exact ha)
    filter_upwards [self_mem_nhdsWithin,hnear] with q hq hqa
    change a < w q
    rw [heq hq]
    exact hqa
  refine ⟨w,continuousOn_iff_lower_upperSemicontinuousOn.mpr ⟨hwl,hw.1⟩,?_,⟨hw.2.2.2,?_⟩,hwb⟩
  · intro q hq
    apply le_antisymm (hw.2.2.1 q hq)
    change G q ≤ w q
    rw [heq (perronBoundary_subset_slab hq)]
    exact perron_lowerSolution_boundary hn hell hL hE h0 hB hG hbG hne q hq
  · exact viscositySuper_eqOn_open (perronOpen_isOpen n)
      (heq.mono perronOpen_subset_slab) hvs

end Yau.LeafProofs.L05Aux
