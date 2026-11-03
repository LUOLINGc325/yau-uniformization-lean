import Yau.LeafProofs.L05PerronEnvelope
import Yau.LeafProofs.L05PerronQuartic

noncomputable section

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

set_option maxHeartbeats 1800000 in
theorem perron_upperSup_sub {n : ℕ} {C Q : Set (Point n)}
    (hQ : IsOpen Q) (hQC : Q ⊆ C) {F : Sym n → ℝ} (hF : Continuous F)
    {S : Set (Point n → ℝ)} (hne : S.Nonempty) {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ w ∈ S, ∀ p ∈ C, |w p| ≤ M)
    (husc : ∀ w ∈ S, UpperSemicontinuousOn w C)
    (hsub : ∀ w ∈ S, viscositySub Q (fun H _ => F H) (fun _ => 0) w) :
    viscositySub Q (fun H _ => F H) (fun _ => 0)
      (perronUpper C (perronFamilySup S)) := by
  let U := perronFamilySup S
  let W := perronUpper C U
  have hbU : ∀ q ∈ C, |U q| ≤ M := fun q hq => perron_familySup_bounds hne hb hq
  intro p hp phi hphi ht
  have hpC := hQC hp
  let phi1 := fun q : Point n => phi q+perronQuartic p q
  have hquart : ContDiffAt ℝ 2 (perronQuartic p) p := (perronQuartic_smooth p).contDiffAt.of_le (by simp)
  have hp1 : ContDiffAt ℝ 2 phi1 p := hphi.add hquart
  obtain ⟨V,hVo,hpV,hV2,hTcont,hHcont⟩ := perron_local_c2_jets hp1
  have hgood : ∀ᶠ q in 𝓝 p, q ∈ Q ∧ q ∈ V ∧ W q ≤ phi q := by
    filter_upwards [hQ.mem_nhds hp,hVo.mem_nhds hpV,ht.2] with q hqQ hqV hqphi
    exact ⟨hqQ,hqV,hqphi⟩
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let r := R/2
  have hr : 0 < r := by dsimp only [r]; positivity
  let K := Metric.closedBall p r
  have hK : IsCompact K := isCompact_closedBall p r
  have hpK : p ∈ K := Metric.mem_closedBall_self hr.le
  have hKgood (q : Point n) (hq : q ∈ K) : q ∈ Q ∧ q ∈ V ∧ W q ≤ phi q :=
    hball (Metric.closedBall_subset_ball (show r < R by dsimp only [r]; linarith) hq)
  have hKC : K ⊆ C := fun q hq => hQC (hKgood q hq).1
  have hsep (q : Point n) (hq : q ∈ K) : W q-phi1 q ≤ -(dist q p)^4 := by
    have hW := (hKgood q hq).2.2
    have hquartic := perronQuartic_distance p q
    dsimp only [phi1]
    linarith
  obtain ⟨q,hqC,hqt,hUval⟩ := perron_upper_recovery hbU hpC
  have hchoose (j : ℕ) : ∃ w ∈ S, U (q j)-((j:ℝ)+1)⁻¹ < w (q j) :=
    perron_familySup_approx hne (q j) (by positivity)
  choose w hw hwclose using hchoose
  have hr0 : Tendsto (fun j : ℕ => ((j:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hwmember (j : ℕ) : w j (q j) ≤ U (q j) := perron_member_le_familySup hb (hw j) (hqC j)
  have hgap : Tendsto (fun j => U (q j)-w j (q j)) atTop (𝓝 0) := by
    apply squeeze_zero (fun j => sub_nonneg.mpr (hwmember j)) _ hr0
    intro j
    linarith [hwclose j]
  have hwval : Tendsto (fun j => w j (q j)) atTop (𝓝 (W p)) := by
    have hh := hUval.sub hgap
    simpa only [sub_sub_cancel,sub_zero] using hh
  have hphi1p : phi1 p=W p := by
    dsimp only [phi1]
    rw [perronQuartic_center,add_zero]
    exact ht.1
  have hphiVal : Tendsto (fun j => phi1 (q j)) atTop (𝓝 (W p)) := by
    rw [←hphi1p]
    exact hp1.continuousAt.tendsto.comp hqt
  have hlowT : Tendsto (fun j => w j (q j)-phi1 (q j)) atTop (𝓝 0) := by
    simpa only [sub_self] using hwval.sub hphiVal
  have hphiCont : ContinuousOn phi1 K := by
    intro x hx
    exact (hV2 x (hKgood x hx).2.1).continuousAt.continuousWithinAt
  have hmaxExists (j : ℕ) : ∃ y ∈ K, IsMaxOn (fun x => w j x-phi1 x) K y := by
    have hu : UpperSemicontinuousOn (fun x => w j x-phi1 x) K := by
      convert! ((husc (w j) (hw j)).mono hKC).add hphiCont.neg.upperSemicontinuousOn using 1 <;>
        simp only [Pi.neg_apply,sub_eq_add_neg]
    exact hu.exists_isMaxOn ⟨p,hpK⟩ hK
  choose y hy hmax using hmaxExists
  let m := fun j => w j (y j)-phi1 (y j)
  have hmdist (j : ℕ) : m j ≤ -(dist (y j) p)^4 := by
    have hwW : w j (y j) ≤ W (y j) :=
      (perron_member_le_familySup hb (hw j) (hKC (hy j))).trans (perron_upper_bounds hbU (hKC (hy j))).1
    exact (sub_le_sub_right hwW (phi1 (y j))).trans (hsep (y j) (hy j))
  have hmnon (j : ℕ) : m j ≤ 0 := (hmdist j).trans (neg_nonpos.mpr (pow_nonneg dist_nonneg _))
  have hqK : ∀ᶠ j in atTop, q j ∈ K := by
    have hn := hqt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
    filter_upwards [hn] with j hj
    exact Metric.ball_subset_closedBall hj
  have hnegm : Tendsto (fun j => -m j) atTop (𝓝 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall (fun j => neg_nonneg.mpr (hmnon j))) _
      (by simpa only [neg_zero] using hlowT.neg)
    filter_upwards [hqK] with j hj
    have hh := hmax j hj
    change w j (q j)-phi1 (q j) ≤ m j at hh
    exact neg_le_neg hh
  have hyt : Tendsto y atTop (𝓝 p) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    have hev : ∀ᶠ j in atTop, -m j < eps^4 := hnegm (eventually_lt_nhds (pow_pos heps 4))
    filter_upwards [hev] with j hj
    by_contra hfail
    have hh := pow_le_pow_left₀ heps.le (le_of_not_gt hfail) 4
    linarith [hmdist j]
  have hyBall : ∀ᶠ j in atTop, y j ∈ Metric.ball p r :=
    hyt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hineq : ∀ᶠ j in atTop, timeD Set.univ phi1 (y j)-F (hessian phi1 (y j)) ≤ 0 := by
    filter_upwards [hyBall] with j hj
    have htest : touchAbove (fun x => phi1 x-(-m j)) (w j) (y j) := by
      refine ⟨by dsimp only [m]; ring,?_⟩
      have hnear : K ∈ 𝓝 (y j) := Metric.closedBall_mem_nhds_of_mem hj
      filter_upwards [hnear] with x hx
      have hh := hmax j hx
      change w j x-phi1 x ≤ m j at hh
      change w j x ≤ phi1 x-(-m j)
      linarith only [hh]
    have hc : ContDiffAt ℝ 2 (fun x => phi1 x-(-m j)) (y j) :=
      (hV2 (y j) (hKgood (y j) (hy j)).2.1).sub contDiffAt_const
    have hh := hsub (w j) (hw j) (y j) (hKgood (y j) (hy j)).1 _ hc htest
    change timeD Set.univ (fun x => phi1 x-(-m j)) (y j)-
      F (hessian (fun x => phi1 x-(-m j)) (y j)) ≤ 0 at hh
    rwa [timeD_sub_const,hessian_sub_const] at hh
  have hyV : ∀ᶠ j in atTop, y j ∈ V := hyt (hVo.mem_nhds hpV)
  have hytV : Tendsto y atTop (𝓝[V] p) := tendsto_nhdsWithin_iff.mpr ⟨hyt,hyV⟩
  have htime := (hTcont p hpV).tendsto.comp hytV
  have hess := (hHcont p hpV).tendsto.comp hytV
  have hres : timeD Set.univ phi1 p-F (hessian phi1 p) ≤ 0 :=
    le_of_tendsto (htime.sub ((hF.tendsto _).comp hess)) hineq
  change timeD Set.univ (fun q => phi q+perronQuartic p q) p-
    F (hessian (fun q => phi q+perronQuartic p q) p) ≤ 0 at hres
  rwa [perron_timeD_add hphi hquart,perron_hessian_add hphi hquart,
    perronQuartic_timeD_zero,perronQuartic_hessian_zero,add_zero,add_zero] at hres

end Yau.LeafProofs.L05Aux
