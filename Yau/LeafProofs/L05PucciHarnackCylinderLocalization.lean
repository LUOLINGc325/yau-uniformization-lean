import Yau.LeafProofs.L05PucciHarnackLocalization
import Yau.LeafProofs.L05PucciHarnackScaledABP

open Filter MeasureTheory Set
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_open_subset_closed {n : ℕ} {c : Space n} {R a T : ℝ} :
    harnackOpen c R a T ⊆ harnackClosed c R a T := by
  rintro z ⟨hx,ht⟩
  exact ⟨Metric.ball_subset_closedBall hx,ht.1.le,ht.2.le⟩

theorem harnack_boundary_subset_closed {n : ℕ} {c : Space n} {R a T : ℝ}
    (hT : 0 ≤ T) {z : Point n} (hz : z∈harnackBoundary c R a T) :
    z∈harnackClosed c R a T := by
  rcases hz with hz | hz
  · exact ⟨hz.1,by rw [show z.2=a from hz.2]; exact ⟨le_rfl,by linarith⟩⟩
  · exact ⟨Metric.sphere_subset_closedBall hz.1,hz.2⟩

theorem harnack_cylinder_localized_positive_viscosity {n : ℕ} {ell L : ℝ}
    (hell : 0≤ell) (hL : ell≤L) (c : Space n) {R a T : ℝ}
    {u Phi G : Point n → ℝ} {M : ℝ}
    (hu : ContinuousOn u (harnackClosed c R a T) ∧
      (∀ z∈harnackClosed c R a T, 0≤u z) ∧
      viscositySuper (harnackOpen c R a T)
        (fun H _ => harnackPucciMinus ell L H) (fun _ => 0) u) (hPhi : ContDiff ℝ 2 Phi)
    (hGnonneg : ∀ z∈harnackClosed c R a T, 0≤G z)
    (hM : ∀ z∈harnackClosed c R a T, Phi z≤M)
    (hRes : ∀ z∈harnackOpen c R a T, timeD univ Phi z-harnackPucciMinus ell L (hessian Phi z)≤G z) :
    viscositySub (harnackOpen c R a T) (fun H _ => pucciPlus ell L H)
      (fun z => G z*harnackSourceClip u M z) (harnackLocalizedPositive Phi u) := by
  have hOriginal := harnack_smooth_minus_super_sub hell hL (fun _ _ => hPhi.contDiffAt) hu.2.2 hRes
  intro p hp psi hpsi ht
  have hpD := harnack_open_subset_closed hp
  by_cases hw : 0<harnackLocalizedPositive Phi u p
  · have hPos : 0<Phi p-u p-1/2 := by
      simpa only [harnackLocalizedPositive,lt_max_iff,lt_self_iff_false,or_false] using hw
    have hNhdD : harnackClosed c R a T ∈ 𝓝 p := mem_of_superset
      ((Metric.isOpen_ball.prod isOpen_Ioo).mem_nhds hp) harnack_open_subset_closed
    have hCont : ContinuousAt (fun z => Phi z-u z-1/2) p :=
      (hPhi.continuous.continuousAt.sub (hu.1.continuousAt hNhdD)).sub_const _
    have hLocal : ∀ᶠ z in 𝓝 p, 0<Phi z-u z-1/2 :=
      hCont.preimage_mem_nhds (isOpen_Ioi.mem_nhds hPos)
    have hTest : touchAbove (fun z => psi z+1/2) (fun z => Phi z-u z) p := by
      refine ⟨?_,?_⟩
      · have he := ht.1
        rw [harnackLocalizedPositive,max_eq_left hPos.le] at he
        linarith
      · filter_upwards [hLocal,ht.2] with z hz htz
        rw [harnackLocalizedPositive,max_eq_left hz.le] at htz
        linarith
    have h := hOriginal p hp _ (hpsi.add contDiffAt_const) hTest
    rw [harnack_timeD_add_const,harnack_hessian_add_const] at h
    have hClip : harnackSourceClip u M p=1 := by
      unfold harnackSourceClip
      have h1 : 1≤2*(M-u p) := by linarith [hM p hpD]
      exact min_eq_left (h1.trans (le_max_left _ _))
    change timeD univ psi p-pucciPlus ell L (hessian psi p)≤G p*harnackSourceClip u M p
    rw [hClip,mul_one]
    exact h
  · have hw0 : harnackLocalizedPositive Phi u p=0 :=
      le_antisymm (not_lt.mp hw) (le_max_right _ _)
    have hTouch : touchAbove psi (fun _ => 0) p := by
      refine ⟨ht.1.trans hw0,?_⟩
      filter_upwards [ht.2] with z hz
      exact (le_max_right _ _).trans hz
    obtain ⟨hTime,hHess⟩ := perron_touch_classical_jets hpsi contDiffAt_const hTouch
    rw [perron_timeD_const] at hTime
    rw [perron_hessian_const,AddSubgroup.coe_zero,sub_zero] at hHess
    have hPucci := harnack_plus_nonneg_of_psd hell hL hHess
    have hg := mul_nonneg (hGnonneg p hpD) (harnack_clip_bounds u M p).1
    rw [hTime]
    linarith

theorem harnack_localized_cylinder_abp
    {n : ℕ} {ell L : ℝ} (hell : 0<ell) (hL : ell≤L)
    (c : Space n) {R a T : ℝ} (hR : 0<R) (hT : 0<T)
    {u Phi G : Point n → ℝ} {E : Set (Point n)} {M K : ℝ}
    (hu : ContinuousOn u (harnackClosed c R a T) ∧
      (∀ z∈harnackClosed c R a T, 0≤u z) ∧
      viscositySuper (harnackOpen c R a T)
        (fun H _ => harnackPucciMinus ell L H) (fun _ => 0) u) (hPhi : ContDiff ℝ 2 Phi)
    (hG : ContinuousOn G (harnackClosed c R a T))
    (hE : MeasurableSet E) (hEQ : E⊆harnackOpen c R a T) (hK : 0<K)
    (hGbounds : ∀ z∈harnackClosed c R a T, 0≤G z ∧ G z≤K)
    (hGzero : ∀ z∈harnackClosed c R a T, z∉E → G z=0)
    (hRes : ∀ z∈harnackOpen c R a T, timeD univ Phi z-harnackPucciMinus ell L (hessian Phi z)≤G z)
    (hBd : ∀ z∈harnackBoundary c R a T, Phi z≤0)
    (hM : ∀ z∈harnackClosed c R a T, Phi z≤M)
    {z : Point n} (hz : z∈harnackClosed c R a T) (hPhi2 : 2≤Phi z) (hu1 : u z≤1) :
    (1/(2*harnackABPCoefficient n ell R T*K))^(2*n+1)≤harnackMu (E ∩ {y | u y≤M}) := by
  let w := harnackLocalizedPositive Phi u
  let g := fun y => G y*harnackSourceClip u M y
  let S := E ∩ {y | u y≤M}
  have hD : IsCompact (harnackClosed c R a T) := (isCompact_closedBall c R).prod isCompact_Icc
  have hQ : IsOpen (harnackOpen c R a T) := Metric.isOpen_ball.prod isOpen_Ioo
  have hQS : harnackOpen c R a T⊆harnackClosed c R a T := harnack_open_subset_closed
  have hSQ : S⊆harnackOpen c R a T := fun y hy => hEQ hy.1
  have hClosedLow : IsClosed (harnackClosed c R a T ∩ {y | u y≤M}) :=
    hu.1.preimage_isClosed_of_isClosed hD.isClosed isClosed_Iic
  have hSmeas : MeasurableSet S := by
    have hEq : S=E ∩ (harnackClosed c R a T ∩ {y | u y≤M}) := by
      ext y
      constructor
      · intro hy
        exact ⟨hy.1,hQS (hEQ hy.1),hy.2⟩
      · intro hy
        exact ⟨hy.1,hy.2.2⟩
    rw [hEq]
    exact hE.inter hClosedLow.measurableSet
  have _hSfinite : (volume : Measure (Point n)) S≠⊤ :=
    ne_top_of_le_ne_top hD.measure_ne_top (measure_mono (hSQ.trans hQS))
  have hwCont : ContinuousOn w (harnackClosed c R a T) :=
    (((hPhi.continuous.continuousOn.sub hu.1).sub continuousOn_const).sup continuousOn_const)
  have hgCont : ContinuousOn g (harnackClosed c R a T) := by
    exact hG.mul (continuousOn_const.inf ((continuousOn_const.sub hu.1).const_mul 2 |>.sup continuousOn_const))
  have hgBounds (y : Point n) (hy : y∈harnackClosed c R a T) : 0≤g y ∧ g y≤K := by
    have hclip := harnack_clip_bounds u M y
    exact ⟨mul_nonneg (hGbounds y hy).1 hclip.1,
      (mul_le_mul_of_nonneg_left hclip.2 (hGbounds y hy).1).trans (by simpa using (hGbounds y hy).2)⟩
  have hgZero (y : Point n) (hy : y∈harnackClosed c R a T) (hys : y∉S) : g y=0 := by
    by_cases hyE : y∈E
    · have huM : M<u y := lt_of_not_ge (fun h => hys ⟨hyE,h⟩)
      have hc : harnackSourceClip u M y=0 := by
        simp only [harnackSourceClip,max_eq_right (by linarith : 2*(M-u y)≤0)]
        norm_num
      simp only [g,hc,mul_zero]
    · simp only [g,hGzero y hy hyE,zero_mul]
  have hwBd : ∀ y∈harnackBoundary c R a T, w y≤0 := by
    intro y hy
    have hyD := harnack_boundary_subset_closed hT.le hy
    dsimp only [w,harnackLocalizedPositive]
    apply max_le _ le_rfl
    linarith [hBd y hy,hu.2.1 y hyD]
  have hSub := harnack_cylinder_localized_positive_viscosity hell.le hL c hu hPhi
    (fun y hy => (hGbounds y hy).1) hM hRes
  have hABP := harnack_scaled_abp hell hL c hR hT hwCont hgCont hwBd hSub hz
  have hwLower : 1/2≤w z := by
    have hm : Phi z-u z-1/2≤w z := le_max_left _ _
    linarith
  let p : ℕ := 2*n+1
  let sourceIntegral : ℝ := ∫ y in harnackOpen c R a T, (max (g y) 0)^p
  have hI : 0 ≤ sourceIntegral := integral_nonneg (fun y => pow_nonneg (le_max_right _ _) _)
  have hInt : IntegrableOn (fun y => (max (g y) 0)^p) (harnackOpen c R a T) :=
    ((hgCont.sup continuousOn_const).pow p).integrableOn_compact hD |>.mono_set hQS
  have hIndInt : IntegrableOn (S.indicator (fun _ : Point n => K^p)) (harnackOpen c R a T) :=
    ((continuousOn_const.integrableOn_compact hD).mono_set hQS).indicator hSmeas
  have hIle : sourceIntegral≤K^p*harnackMu S := by
    calc
      sourceIntegral ≤ ∫ y in harnackOpen c R a T, S.indicator (fun _ : Point n => K^p) y := by
        apply integral_mono_ae hInt hIndInt
        filter_upwards [ae_restrict_mem hQ.measurableSet] with y hy
        have hyD := hQS hy
        by_cases hyS : y∈S
        · rw [indicator_of_mem hyS,max_eq_left (hgBounds y hyD).1]
          exact pow_le_pow_left₀ (hgBounds y hyD).1 (hgBounds y hyD).2 _
        · rw [indicator_of_notMem hyS,hgZero y hyD hyS]
          simp only [max_self,zero_pow (by dsimp only [p]; omega : p≠0)]
          exact le_refl 0
      _ = K^p*harnackMu S := by
        rw [integral_indicator hSmeas,Measure.restrict_restrict hSmeas]
        have hEq : S ∩ harnackOpen c R a T=S := inter_eq_left.mpr hSQ
        rw [hEq]
        rw [setIntegral_const]
        change ((volume : Measure (Point n)) S).toReal*K^p=K^p*((volume : Measure (Point n)) S).toReal
        ring
  have hA := harnack_abpCoefficient_pos n hell hR hT
  have hRoot : 1/2≤harnackABPCoefficient n ell R T*sourceIntegral^(1/(p : ℝ)) := hwLower.trans hABP
  have hPower := pow_le_pow_left₀ (by norm_num : (0 : ℝ)≤1/2) hRoot p
  rw [mul_pow,show (sourceIntegral^(1/(p : ℝ)))^p=sourceIntegral from by
    simpa only [one_div] using Real.rpow_inv_natCast_pow hI (by dsimp only [p]; omega : p≠0)] at hPower
  have hTotal : (1/2 : ℝ)^p≤(harnackABPCoefficient n ell R T*K)^p*harnackMu S := by
    calc
      _ ≤ (harnackABPCoefficient n ell R T)^p*sourceIntegral := hPower
      _ ≤ (harnackABPCoefficient n ell R T)^p*(K^p*harnackMu S) := mul_le_mul_of_nonneg_left hIle (pow_nonneg hA.le _)
      _ = _ := by rw [mul_pow]; ring
  have hEq : (1/(2*harnackABPCoefficient n ell R T*K))^p=(1/2 : ℝ)^p/(harnackABPCoefficient n ell R T*K)^p := by
    rw [← div_pow]
    congr 1
    field_simp
  rw [hEq]
  apply (div_le_iff₀ (pow_pos (mul_pos hA hK) p)).mpr
  simpa only [mul_comm] using hTotal

end Yau.LeafProofs.L05Aux
