import Yau.LeafProofs.L05AutonomousDifferences
import Yau.LeafProofs.L05PerronQuartic

noncomputable section
open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- The set contains the actual continuous viscosity subsolutions. -/
theorem auto_subsolutions_convex {n : ℕ} {Q : Set (Point n)} {ell L : ℝ}
    {F : Sym n → ℝ} (hQ : IsOpen Q) (hell : 0≤ell) (hL : ell≤L)
    (hE : globalElliptic F ell L) (hC : ConcaveOn ℝ univ F) :
    Convex ℝ {u : Point n → ℝ | ContinuousOn u Q ∧
      viscositySub Q (fun H _ => F H) (fun _ => 0) u} := by
  intro u hu v hv a b ha hb hab
  constructor
  · exact (continuousOn_const.mul hu.1).add (continuousOn_const.mul hv.1)
  have htheta : a∈Icc 0 1 := ⟨ha,by linarith only [hb,hab]⟩
  have hh := jet_autonomous_convex_combination_sub hQ hell hL hE hC hu.1 hv.1 hu.2 hv.2 htheta
  convert hh using 1
  funext p
  change a*u p+b*v p=a*u p+(1-a)*v p
  have heq : b=1-a := by linarith only [hab]
  rw [heq]

/-- Finite probability averages retain the actual viscosity subsolution property. -/
theorem auto_finite_probability_sub {n : ℕ} {ι : Type*} (s : Finset ι)
    {Q : Set (Point n)} {ell L : ℝ} {F : Sym n → ℝ}
    (hQ : IsOpen Q) (hell : 0≤ell) (hL : ell≤L) (hE : globalElliptic F ell L)
    (hC : ConcaveOn ℝ univ F) (w : ι → ℝ) (hw : ∀ i∈s, 0≤w i)
    (hsum : ∑ i∈s, w i=1) (v : ι → Point n → ℝ)
    (hv : ∀ i∈s, ContinuousOn (v i) Q)
    (hsub : ∀ i∈s, viscositySub Q (fun H _ => F H) (fun _ => 0) (v i)) :
    ContinuousOn (fun p => ∑ i∈s, w i*v i p) Q ∧
      viscositySub Q (fun H _ => F H) (fun _ => 0) (fun p => ∑ i∈s, w i*v i p) := by
  have hh := (auto_subsolutions_convex hQ hell hL hE hC).sum_mem hw hsum
    (fun i hi => ⟨hv i hi,hsub i hi⟩)
  have heq : (∑ i∈s, w i • v i)=(fun p => ∑ i∈s, w i*v i p) := by
    funext p
    simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  rw [heq] at hh
  exact hh

/-- Uniform convergence controls errors along any sequence of points in its domain. -/
theorem auto_uniform_error_along {n : ℕ} {K : Set (Point n)}
    {v : ℕ → Point n → ℝ} {u : Point n → ℝ}
    (hlim : TendstoUniformlyOn v u atTop K) (y : ℕ → Point n) (hy : ∀ j, y j∈K) :
    Tendsto (fun j => v j (y j)-u (y j)) atTop (𝓝 0) := by
  apply Metric.tendsto_nhds.mpr
  intro eps heps
  filter_upwards [Metric.tendstoUniformlyOn_iff.mp hlim eps heps] with j hj
  have hh := hj (y j) (hy j)
  simpa only [Real.dist_eq,sub_zero,abs_sub_comm] using hh

/-- Locally uniform limits are viscosity subsolutions. Contacts and jets are the
actual native tests, strictified by the already proved quartic polynomial. -/
theorem auto_locally_uniform_sub {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ}
    (hQ : IsOpen Q) (hF : Continuous F) {v : ℕ → Point n → ℝ} {u : Point n → ℝ}
    (hv : ∀ j, ContinuousOn (v j) Q)
    (hsub : ∀ j, viscositySub Q (fun H _ => F H) (fun _ => 0) (v j))
    (hlim : TendstoLocallyUniformlyOn v u atTop Q) :
    viscositySub Q (fun H _ => F H) (fun _ => 0) u := by
  have hu : ContinuousOn u Q := hlim.continuousOn (Filter.Eventually.of_forall hv).frequently
  intro p hp phi hphi ht
  let phi1 : Point n → ℝ := fun q => phi q+perronQuartic p q
  have hquart : ContDiffAt ℝ 2 (perronQuartic p) p :=
    (perronQuartic_smooth p).contDiffAt.of_le (by simp)
  have hp1 : ContDiffAt ℝ 2 phi1 p := hphi.add hquart
  obtain ⟨V,hVo,hpV,hV2,hTcont,hHcont⟩ := perron_local_c2_jets hp1
  have hgood : ∀ᶠ q in 𝓝 p, q∈Q ∧ q∈V ∧ u q≤phi q := by
    filter_upwards [hQ.mem_nhds hp,hVo.mem_nhds hpV,ht.2] with q hqQ hqV hqphi
    exact ⟨hqQ,hqV,hqphi⟩
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let r := R/2
  have hr : 0<r := by dsimp only [r]; positivity
  let K := Metric.closedBall p r
  have hK : IsCompact K := isCompact_closedBall p r
  have hpK : p∈K := Metric.mem_closedBall_self hr.le
  have hKgood (q : Point n) (hq : q∈K) : q∈Q ∧ q∈V ∧ u q≤phi q :=
    hball (Metric.closedBall_subset_ball (by dsimp only [r]; linarith only [hR]) hq)
  have hKQ : K⊆Q := fun q hq => (hKgood q hq).1
  have hsep (q : Point n) (hq : q∈K) : u q-phi1 q≤-(dist q p)^4 := by
    have hh := (hKgood q hq).2.2
    have hdist := perronQuartic_distance p q
    dsimp only [phi1]
    linarith only [hh,hdist]
  have hphiCont : ContinuousOn phi1 K := fun x hx =>
    (hV2 x (hKgood x hx).2.1).continuousAt.continuousWithinAt
  have hmaxExists (j : ℕ) : ∃ y∈K, IsMaxOn (fun x => v j x-phi1 x) K y :=
    hK.exists_isMaxOn ⟨p,hpK⟩ (((hv j).mono hKQ).sub hphiCont)
  choose y hy hmax using hmaxExists
  let m : ℕ → ℝ := fun j => v j (y j)-phi1 (y j)
  have hUK : TendstoUniformlyOn v u atTop K :=
    (tendstoLocallyUniformlyOn_iff_forall_isCompact hQ).mp hlim K hKQ hK
  have herr := auto_uniform_error_along hUK y hy
  have hpval : Tendsto (fun j => v j p-phi1 p) atTop (𝓝 0) := by
    have heq : u p=phi1 p := by
      dsimp only [phi1]
      rw [perronQuartic_center,add_zero,ht.1]
    simpa only [heq,sub_self] using (hlim.tendsto_at hp).sub_const (phi1 p)
  have hupper (j : ℕ) : m j≤(v j (y j)-u (y j))-(dist (y j) p)^4 := by
    have hh := hsep (y j) (hy j)
    dsimp only [m]
    linarith only [hh]
  have hlower (j : ℕ) : v j p-phi1 p≤ m j := hmax j hpK
  have hyt : Tendsto y atTop (𝓝 p) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    have hzero : Tendsto (fun j => (v j (y j)-u (y j))-(v j p-phi1 p)) atTop (𝓝 0) := by
      simpa only [sub_zero] using herr.sub hpval
    have hev : ∀ᶠ j in atTop,
        (v j (y j)-u (y j))-(v j p-phi1 p)<eps^4 :=
      hzero (eventually_lt_nhds (pow_pos heps 4))
    filter_upwards [hev] with j hj
    by_contra hfail
    have hh := pow_le_pow_left₀ heps.le (le_of_not_gt hfail) 4
    linarith only [hh,hupper j,hlower j,hj]
  have hyBall : ∀ᶠ j in atTop, y j∈Metric.ball p r :=
    hyt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hineq : ∀ᶠ j in atTop, timeD univ phi1 (y j)-F (hessian phi1 (y j))≤0 := by
    filter_upwards [hyBall] with j hj
    have htest : touchAbove (fun x => phi1 x+m j) (v j) (y j) := by
      refine ⟨by dsimp only [m]; ring,?_⟩
      have hnear : K∈𝓝 (y j) := Metric.closedBall_mem_nhds_of_mem hj
      filter_upwards [hnear] with x hx
      have hh := hmax j hx
      change v j x-phi1 x≤ m j at hh
      change v j x≤phi1 x+m j
      linarith only [hh]
    have hc : ContDiffAt ℝ 2 (fun x => phi1 x+m j) (y j) :=
      (hV2 (y j) (hKgood (y j) (hy j)).2.1).add contDiffAt_const
    have hh := hsub j (y j) (hKgood (y j) (hy j)).1 _ hc htest
    rwa [harnack_timeD_add_const,harnack_hessian_add_const] at hh
  have hyV : ∀ᶠ j in atTop, y j∈V := hyt (hVo.mem_nhds hpV)
  have hytV : Tendsto y atTop (𝓝[V] p) := tendsto_nhdsWithin_iff.mpr ⟨hyt,hyV⟩
  have htime := (hTcont p hpV).tendsto.comp hytV
  have hess := (hHcont p hpV).tendsto.comp hytV
  have hres : timeD univ phi1 p-F (hessian phi1 p)≤0 :=
    le_of_tendsto (htime.sub ((hF.tendsto _).comp hess)) hineq
  change timeD univ (fun q => phi q+perronQuartic p q) p-
    F (hessian (fun q => phi q+perronQuartic p q) p)≤0 at hres
  rwa [perron_timeD_add hphi hquart,perron_hessian_add hphi hquart,
    perronQuartic_timeD_zero,perronQuartic_hessian_zero,add_zero,add_zero] at hres

theorem auto_negate_test_jets {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hphi : ContDiffAt ℝ 2 phi p) :
    timeD univ (fun z => -phi z) p = -timeD univ phi p ∧
      hessian (fun z => -phi z) p = -hessian phi p := by
  constructor
  · simpa only [neg_one_mul] using harnack_timeD_const_mul hphi (-1)
  · simpa only [neg_one_mul,neg_one_smul] using harnack_hessian_const_mul hphi (-1)

theorem auto_super_iff_neg_sub {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ}
    {w : Point n → ℝ} :
    viscositySuper Q (fun H _ => F H) (fun _ => 0) w ↔
      viscositySub Q (fun H _ => -F (-H)) (fun _ => 0) (fun p => -w p) := by
  constructor
  · intro hw p hp phi hphi ht
    have hneg : ContDiffAt ℝ 2 (fun z => -phi z) p := hphi.neg
    have htouch : touchBelow (fun z => -phi z) w p := by
      refine ⟨by have hh := ht.1; change phi p=-w p at hh; linarith only [hh],?_⟩
      filter_upwards [ht.2] with q hq
      change -w q≤phi q at hq
      change -phi q≤w q
      linarith only [hq]
    have hh := hw p hp _ hneg htouch
    rw [(auto_negate_test_jets hphi).1,(auto_negate_test_jets hphi).2] at hh
    change timeD univ phi p-(-F (-hessian phi p))≤0
    linarith only [hh]
  intro hw p hp phi hphi ht
  have hneg : ContDiffAt ℝ 2 (fun z => -phi z) p := hphi.neg
  have htouch : touchAbove (fun z => -phi z) (fun p => -w p) p := by
    refine ⟨by have hh := ht.1; change phi p=w p at hh; linarith only [hh],?_⟩
    filter_upwards [ht.2] with q hq
    change phi q≤w q at hq
    change -w q≤-phi q
    linarith only [hq]
  have hh := hw p hp _ hneg htouch
  rw [(auto_negate_test_jets hphi).1,(auto_negate_test_jets hphi).2] at hh
  change -timeD univ phi p-(-F (-(-hessian phi p)))≤0 at hh
  rw [neg_neg] at hh
  change 0≤timeD univ phi p-F (hessian phi p)
  linarith only [hh]

theorem auto_locally_uniform_super {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ}
    (hQ : IsOpen Q) (hF : Continuous F) {v : ℕ → Point n → ℝ} {u : Point n → ℝ}
    (hv : ∀ j, ContinuousOn (v j) Q)
    (hsuper : ∀ j, viscositySuper Q (fun H _ => F H) (fun _ => 0) (v j))
    (hlim : TendstoLocallyUniformlyOn v u atTop Q) :
    viscositySuper Q (fun H _ => F H) (fun _ => 0) u := by
  apply auto_super_iff_neg_sub.mpr
  exact auto_locally_uniform_sub hQ (hF.comp continuous_neg).neg
    (fun j => (hv j).neg) (fun j => auto_super_iff_neg_sub.mp (hsuper j)) hlim.neg

end Yau.LeafProofs.L05AutonomousAux
