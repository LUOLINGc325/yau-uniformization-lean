import Yau.LeafProofs.L05PucciHarnack
import Yau.LeafProofs.L05AutonomousDifferences

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The actual normalized early-slab Lp mean; no essential extremum is assumed. -/
def autoLpMean {n : ℕ} (E : Set (Point n)) (p : ℝ) (v : Point n → ℝ) : ℝ :=
  ((∫ y in E, (v y)^p)/((volume : Measure (Point n)) E).toReal)^(1/p)

/-- The zero-source form is derived from the exact proved inhomogeneous Harnack endpoint. -/
theorem auto_weak_harnack_homogeneous {n : ℕ} (hn : 0< n) {ell L : ℝ}
    (hell : 0< ell) (hL : ell≤ L) :
    ∃ p C : ℝ, 0< p ∧ p<1 ∧ 0< C ∧ ∀ v : Point n → ℝ,
      ContinuousOn v (unitClosed n) → (∀ z∈unitClosed n, 0≤ v z) →
      viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) v →
      ∀ z∈harnackQplus n, autoLpMean (harnackQminus n) p v≤ C*v z := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := pucci_weak_harnack hn hell hL
  refine ⟨p,C,hp,hp1,hC,?_⟩
  intro v hv hv0 hSuper z hz
  have hzero : harnackSuper0 ell L v := ⟨hv,hv0,hSuper⟩
  have hsmall : ∀ eps : ℝ, 0< eps → autoLpMean (harnackQminus n) p v≤ C*(v z+eps) := by
    intro eps heps
    let u : Point n → ℝ := fun y => v y/eps
    have hu : harnackSuper0 ell L u := harnack_super0_div hell.le hL heps hzero
    have huSuper : viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H)) (fun _ => -1) u := by
      intro y hy phi hphi ht
      have hh := hu.2.2 y hy phi hphi ht
      change 0≤ timeD univ phi y-(-pucciPlus ell L (-hessian phi y)) at hh
      change -1≤ timeD univ phi y-(-pucciPlus ell L (-hessian phi y))
      linarith only [hh]
    have hwh := hWH u hu.1 hu.2.1 huSuper z hz
    have hscale := harnack_moment_norm_scale hu.1 hv hu.2.1 hv0
      (harnack_qminus_isOpen n).measurableSet harnack_qminus_subset_unitClosed
      (harnack_qminus_mu_pos n) heps hp (fun y _ => by
        dsimp only [u]
        rw [mul_div_cancel₀ _ heps.ne'])
    change autoLpMean (harnackQminus n) p v≤ eps*autoLpMean (harnackQminus n) p u at hscale
    calc
      _ ≤ eps*autoLpMean (harnackQminus n) p u := hscale
      _ ≤ eps*(C*(v z/eps+1)) := mul_le_mul_of_nonneg_left hwh heps.le
      _ = C*(v z+eps) := by field_simp
  apply le_of_forall_pos_le_add
  intro eps heps
  have hh := hsmall (eps/C) (div_pos heps hC)
  have heq : C*(v z+eps/C)=C*v z+eps := by field_simp
  rwa [heq] at hh

/-- The two nonnegative deficits retain their full amplitude after taking p-th powers. -/
theorem auto_rpow_deficit_sum {a b p : ℝ} (ha : 0≤ a) (hb : 0≤ b) (hp : 0< p) (hp1 : p≤1) :
    (a+b)^p≤ a^p+b^p := by
  by_cases hzero : a+b=0
  · have ha0 : a=0 := by linarith only [ha,hb,hzero]
    have hb0 : b=0 := by linarith only [ha,hb,hzero]
    simp [ha0,hb0,Real.zero_rpow hp.ne']
  have hpos : 0< a+b := lt_of_le_of_ne (add_nonneg ha hb) (Ne.symm hzero)
  have hfirst := Real.self_le_rpow_of_le_one (div_nonneg ha hpos.le)
    ((div_le_one hpos).mpr (by linarith only [hb])) hp1
  have hsecond := Real.self_le_rpow_of_le_one (div_nonneg hb hpos.le)
    ((div_le_one hpos).mpr (by linarith only [ha])) hp1
  rw [Real.div_rpow ha hpos.le] at hfirst
  rw [Real.div_rpow hb hpos.le] at hsecond
  have hh := add_le_add hfirst hsecond
  rw [← add_div,div_self hzero,← add_div] at hh
  simpa only [one_mul] using (le_div_iff₀ (Real.rpow_pos_of_pos hpos p)).mp hh

/-- A true one-step oscillation contraction follows from the two actual deficit equations. -/
theorem auto_pucci_late_contraction {n : ℕ} (hn : 0< n) {ell L : ℝ}
    (hell : 0< ell) (hL : ell≤ L) :
    ∃ c : ℝ, 0< c ∧ c<1 ∧ ∀ (w : Point n → ℝ) (m M : ℝ),
      ContinuousOn w (unitClosed n) → (∀ z∈unitClosed n, m≤ w z ∧ w z≤ M) →
      autoPucci ell L (unitOpen n) w →
      ∀ z∈harnackQplus n, ∀ q∈harnackQplus n, w z-w q≤(1-c)*(M-m) := by
  obtain ⟨p,C,hp,hp1,hC,hWH⟩ := auto_weak_harnack_homogeneous hn hell hL
  let theta := (1/2 : ℝ)^(1/p)
  let c := min (1/2) (theta/C)
  have ht : 0< theta := Real.rpow_pos_of_pos (by norm_num) _
  have hc : 0< c := lt_min (by norm_num) (div_pos ht hC)
  have hc1 : c<1 := lt_of_le_of_lt (min_le_left _ _) (by norm_num)
  refine ⟨c,hc,hc1,?_⟩
  intro w m M hw hb hP
  let a : Point n → ℝ := fun z => M-w z
  let b : Point n → ℝ := fun z => w z-m
  have ha : ContinuousOn a (unitClosed n) := continuousOn_const.sub hw
  have hbcont : ContinuousOn b (unitClosed n) := hw.sub continuousOn_const
  have ha0 : ∀ z∈unitClosed n, 0≤ a z := fun z hz => sub_nonneg.mpr (hb z hz).2
  have hb0 : ∀ z∈unitClosed n, 0≤ b z := fun z hz => sub_nonneg.mpr (hb z hz).1
  have haSuper : viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) a :=
    auto_pucci_deficit_super hP.1 M
  have hbSuper : viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) b := by
    convert viscositySuper_add_const hP.2 (-m) using 1
  let E := harnackQminus n
  let mu := harnackMu E
  have hE : MeasurableSet E := (harnack_qminus_isOpen n).measurableSet
  have hmu : 0< mu := harnack_qminus_mu_pos n
  have hcompact : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hai : IntegrableOn (fun z => (a z)^p) E :=
    ((ha.rpow_const (fun _ _ => Or.inr hp.le)).integrableOn_compact hcompact).mono_set harnack_qminus_subset_unitClosed
  have hbi : IntegrableOn (fun z => (b z)^p) E :=
    ((hbcont.rpow_const (fun _ _ => Or.inr hp.le)).integrableOn_compact hcompact).mono_set harnack_qminus_subset_unitClosed
  obtain ⟨z₀,hz₀⟩ := harnack_qminus_nonempty n
  have hMm : 0≤ M-m := by
    have hh := hb z₀ (harnack_qminus_subset_unitClosed hz₀)
    linarith only [hh.1,hh.2]
  have hsum : mu*(M-m)^p≤(∫ z in E, (a z)^p)+(∫ z in E, (b z)^p) := by
    have hconst : IntegrableOn (fun _ : Point n => (M-m)^p) E :=
      integrableOn_const (C := (M-m)^p) (hs := harnack_qminus_measure_ne_top n)
    have hh := integral_mono_ae hconst (hai.add hbi) (by
      filter_upwards [ae_restrict_mem hE] with z hz
      have hz0 := harnack_qminus_subset_unitClosed hz
      have hpw := auto_rpow_deficit_sum (ha0 z hz0) (hb0 z hz0) hp hp1.le
      have heq : a z+b z=M-m := by dsimp only [a,b]; ring
      simpa only [heq,Pi.add_apply] using hpw)
    change (∫ _ : Point n in E, (M-m)^p)≤∫ z in E, (a z)^p+(b z)^p at hh
    rw [integral_add hai hbi] at hh
    simpa only [setIntegral_const,smul_eq_mul,mu,harnackMu,measureReal_def] using hh
  have hchoice : (M-m)^p/2≤(∫ z in E, (a z)^p)/mu ∨
      (M-m)^p/2≤(∫ z in E, (b z)^p)/mu := by
    by_contra hno
    push Not at hno
    have h1 := (div_lt_iff₀ hmu).mp hno.1
    have h2 := (div_lt_iff₀ hmu).mp hno.2
    nlinarith only [hsum,h1,h2]
  have hroot : ((M-m)^p/2)^(1/p)=theta*(M-m) := by
    rw [Real.div_rpow (Real.rpow_nonneg hMm p) (by norm_num),← Real.rpow_mul hMm]
    rw [show p*(1/p)=1 from by field_simp [hp.ne'],Real.rpow_one]
    dsimp only [theta]
    rw [Real.div_rpow (by norm_num) (by norm_num),Real.one_rpow]
    ring
  have hforce (v : Point n → ℝ) (hv : ContinuousOn v (unitClosed n)) (hv0 : ∀ z∈unitClosed n, 0≤ v z)
      (hvSuper : viscositySuper (unitOpen n) (fun H _ => -pucciPlus ell L (-H)) (fun _ => 0) v)
      (hvlarge : (M-m)^p/2≤(∫ z in E, (v z)^p)/mu) :
      ∀ z∈harnackQplus n, c*(M-m)≤ v z := by
    have hmean := Real.rpow_le_rpow (div_nonneg (Real.rpow_nonneg hMm p) (by norm_num))
      hvlarge (one_div_pos.mpr hp).le
    rw [hroot] at hmean
    intro z hz
    have hwh := hWH v hv hv0 hvSuper z hz
    have hlarge : theta*(M-m)≤ C*v z := hmean.trans hwh
    calc
      c*(M-m) ≤ (theta/C)*(M-m) := mul_le_mul_of_nonneg_right (min_le_right _ _) hMm
      _ = (theta*(M-m))/C := by ring
      _ ≤ v z := (div_le_iff₀ hC).mpr (by simpa only [mul_comm C] using hlarge)
  intro z hz q hq
  rcases hchoice with hchoice | hchoice
  · have hupper := hforce a ha ha0 haSuper hchoice z hz
    have hlower := (hb q (harnack_qplus_subset_unitClosed hq)).1
    dsimp only [a] at hupper
    nlinarith only [hupper,hlower]
  · have hlower := hforce b hbcont hb0 hbSuper hchoice q hq
    have hupper := (hb z (harnack_qplus_subset_unitClosed hz)).2
    dsimp only [b] at hlower
    nlinarith only [hupper,hlower]

theorem auto_late_pair_closure {n : ℕ} {w : Point n → ℝ} {K : ℝ}
    (hw : ContinuousOn w (unitClosed n))
    (hpair : ∀ z∈harnackQplus n, ∀ q∈harnackQplus n, w z-w q≤ K) :
    ∀ z∈closure (harnackQplus n), ∀ q∈closure (harnackQplus n), w z-w q≤ K := by
  have hclosed : IsClosed (unitClosed n) :=
    ((isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc).isClosed
  have hsub : closure (harnackQplus n)⊆unitClosed n :=
    closure_minimal harnack_qplus_subset_unitClosed hclosed
  have hfirst : ∀ q∈harnackQplus n, ∀ z∈closure (harnackQplus n), w z-w q≤ K := by
    intro q hq z hz
    exact le_on_closure (fun y hy => hpair y hy q hq)
      ((hw.sub continuousOn_const).mono hsub) continuousOn_const hz
  intro z hz q hq
  exact le_on_closure (fun y hy => hfirst y hy z hz)
    ((continuousOn_const.sub hw).mono hsub) continuousOn_const hq

theorem auto_quarter_closed_subset_late_closure (n : ℕ) :
    autoClosed (0 : Space n) (1/4) 0⊆closure (harnackQplus n) := by
  rw [harnackQplus,closure_prod_eq,closure_ball (0 : Space n) (by norm_num),
    closure_Ioo (by norm_num : (-1/4 : ℝ)≠0)]
  intro z hz
  refine ⟨hz.1,?_⟩
  have ht : -(1/4 : ℝ)^2≤z.2 ∧ z.2≤0 := by simpa only [autoClosed,zero_sub,mem_prod,mem_Icc] using hz.2
  constructor <;> linarith only [ht.1,ht.2]

/-- Quarter-cylinder contraction includes the true top face by continuity alone. -/
theorem auto_pucci_quarter_contraction {n : ℕ} (hn : 0<n) {ell L : ℝ}
    (hell : 0<ell) (hL : ell≤L) :
    ∃ c : ℝ, 0<c ∧ c<1 ∧ ∀ (w : Point n → ℝ) (m M : ℝ),
      ContinuousOn w (unitClosed n) → (∀ z∈unitClosed n, m≤w z ∧ w z≤M) →
      autoPucci ell L (unitOpen n) w →
      ∀ z∈autoClosed (0 : Space n) (1/4) 0,
      ∀ q∈autoClosed (0 : Space n) (1/4) 0, w z-w q≤(1-c)*(M-m) := by
  obtain ⟨c,hc,hc1,hstep⟩ := auto_pucci_late_contraction hn hell hL
  refine ⟨c,hc,hc1,?_⟩
  intro w m M hw hb hP z hz q hq
  exact auto_late_pair_closure hw (hstep w m M hw hb hP) z
    (auto_quarter_closed_subset_late_closure n hz) q (auto_quarter_closed_subset_late_closure n hq)

end Yau.LeafProofs.L05AutonomousAux
