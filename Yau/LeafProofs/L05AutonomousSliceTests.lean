import Yau.LeafProofs.L05AutonomousAverages

noncomputable section
open Filter Set MeasureTheory
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

/-- A native smooth test has its actual time derivative. -/
theorem auto_test_time_hasDerivAt {n : ℕ} {phi : Point n → ℝ} {p : Point n}
    (hphi : ContDiffAt ℝ 2 phi p) :
    HasDerivAt (fun t => phi (p.1,t)) (timeD univ phi p) p.2 := by
  have hline : HasDerivAt (fun t => (p.1,t)) ((0,1) : Point n) p.2 :=
    (hasDerivAt_const p.2 p.1).prodMk (hasDerivAt_id p.2)
  have hd := hphi.differentiableAt (by norm_num)
  rw [timeD_univ_eq_joint hd]
  simpa only [Function.comp_def,Prod.eta] using hd.hasFDerivAt.comp_hasDerivAt p.2 hline

/-- At a true contact, a genuine time derivative of u equals the test derivative.
There is no joint C² hypothesis on u. -/
theorem auto_contact_time_eq {n : ℕ} {u phi : Point n → ℝ} {p : Point n} {V : ℝ}
    (hTime : HasDerivAt (fun t => u (p.1,t)) V p.2)
    (hphi : ContDiffAt ℝ 2 phi p) (ht : touchAbove phi u p) :
    timeD univ phi p=V := by
  have hline : Tendsto (fun t : ℝ => (p.1,t)) (𝓝 p.2) (𝓝 p) := by
    simpa only [Prod.eta,id_eq] using (continuous_const.prodMk continuous_id).tendsto p.2
  have hzero : u (p.1,p.2)-phi (p.1,p.2)=0 := by rw [Prod.eta,ht.1]; ring
  have hmax : IsLocalMax (fun t => u (p.1,t)-phi (p.1,t)) p.2 := by
    change ∀ᶠ t in 𝓝 p.2, u (p.1,t)-phi (p.1,t)≤u (p.1,p.2)-phi (p.1,p.2)
    rw [hzero]
    filter_upwards [hline ht.2] with t ht'
    exact sub_nonpos.mpr ht'
  have hh := hmax.hasDerivAt_eq_zero (hTime.sub (auto_test_time_hasDerivAt hphi))
  linarith only [hh]

theorem auto_sub_at_time_differentiable_contact {n : ℕ} {Q : Set (Point n)}
    {u phi : Point n → ℝ} {F : Sym n → ℝ} {p : Point n} {V : ℝ}
    (hsub : viscositySub Q (fun H _ => F H) (fun _ => 0) u) (hp : p∈Q)
    (hTime : HasDerivAt (fun t => u (p.1,t)) V p.2)
    (hphi : ContDiffAt ℝ 2 phi p) (ht : touchAbove phi u p) :
    V≤F (hessian phi p) := by
  have hh := hsub p hp phi hphi ht
  rw [auto_contact_time_eq hTime hphi ht] at hh
  linarith only [hh]

/-- A time-dependent addend is a literal spatial constant on every slice. -/
theorem auto_hessian_add_time {n : ℕ} (phi : Point n → ℝ) (g : ℝ → ℝ) (p : Point n) :
    hessian (fun q => phi q+g q.2) p=hessian phi p := by
  simp only [hessian,spatialDD,fderiv_add_const]

/-- Quadratic time penalties produce genuine interior contacts converging to the
strict spatial contact. The finite compact bound is used only to choose contacts. -/
theorem auto_time_penalty_contacts {n : ℕ} (p : Point n) {r : ℝ} (hr : 0<r)
    {w : Point n → ℝ} (hw : ContinuousOn w (Metric.closedBall p r)) (hw0 : w p=0)
    (hslice : ∀ q∈Metric.closedBall p r, q.2=p.2 → w q≤-(dist q p)^4) :
    ∃ y : ℕ → Point n,
      (∀ j, y j∈Metric.closedBall p r) ∧ Tendsto y atTop (𝓝 p) ∧
      ∀ j : ℕ, IsMaxOn (fun q => w q-((j:ℝ)+1)*(q.2-p.2)^2)
        (Metric.closedBall p r) (y j) := by
  let K := Metric.closedBall p r
  have hK : IsCompact K := isCompact_closedBall p r
  have hpK : p∈K := Metric.mem_closedBall_self hr.le
  have hc (j : ℕ) : ContinuousOn (fun q : Point n => w q-((j:ℝ)+1)*(q.2-p.2)^2) K :=
    hw.sub (continuousOn_const.mul ((continuous_snd.continuousOn.sub continuousOn_const).pow 2))
  have hmaxExists (j : ℕ) : ∃ y∈K,
      IsMaxOn (fun q : Point n => w q-((j:ℝ)+1)*(q.2-p.2)^2) K y :=
    hK.exists_isMaxOn ⟨p,hpK⟩ (hc j)
  choose y hy hmax using hmaxExists
  obtain ⟨qmax,hqmax,hmaxw⟩ := hK.exists_isMaxOn ⟨p,hpK⟩ hw
  let M := w qmax
  have hM (q : Point n) (hq : q∈K) : w q≤M := hmaxw hq
  have hnonneg (j : ℕ) : 0≤w (y j)-((j:ℝ)+1)*((y j).2-p.2)^2 := by
    have hh := hmax j hpK
    change w p-((j:ℝ)+1)*(p.2-p.2)^2≤w (y j)-((j:ℝ)+1)*((y j).2-p.2)^2 at hh
    simpa only [hw0,sub_self,zero_pow (by norm_num : (2:ℕ)≠0),mul_zero,sub_zero] using hh
  have hwpos (j : ℕ) : 0≤w (y j) := by
    have hcpos : 0≤((j:ℝ)+1)*((y j).2-p.2)^2 := mul_nonneg (Nat.cast_add_one_pos j).le (sq_nonneg _)
    linarith only [hnonneg j,hcpos]
  have htimeSq (j : ℕ) : ((y j).2-p.2)^2≤M/((j:ℝ)+1) := by
    apply (le_div_iff₀ (Nat.cast_add_one_pos j)).mpr
    have hh := hM (y j) (hy j)
    nlinarith only [hnonneg j,hh]
  have hMtend : Tendsto (fun j : ℕ => M/((j:ℝ)+1)) atTop (𝓝 0) := by
    simpa only [one_div,div_eq_mul_inv,mul_zero,one_mul] using
      ((tendsto_const_nhds : Tendsto (fun _ : ℕ => M) atTop (𝓝 M)).mul (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)))
  have htime : Tendsto (fun j => (y j).2) atTop (𝓝 p.2) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [hMtend (eventually_lt_nhds (pow_pos heps 2))] with j hj
    change M/((j:ℝ)+1)<eps^2 at hj
    by_contra hfail
    have habs : eps≤|(y j).2-p.2| := by simpa only [Real.dist_eq] using le_of_not_gt hfail
    have hh := pow_le_pow_left₀ heps.le habs 2
    rw [sq_abs] at hh
    linarith only [hh,htimeSq j,hj]
  let z : ℕ → Point n := fun j => ((y j).1,p.2)
  have hz (j : ℕ) : z j∈K := by
    have hh : max (dist (y j).1 p.1) (dist (y j).2 p.2)≤r := by
      simpa only [K,Metric.mem_closedBall,Prod.dist_eq] using hy j
    change dist (z j) p≤r
    calc
      _ = dist (y j).1 p.1 := by simp only [z,Prod.dist_eq,dist_self,max_eq_left dist_nonneg]
      _ ≤ max (dist (y j).1 p.1) (dist (y j).2 p.2) := le_max_left _ _
      _ ≤ r := hh
  have hdt : Tendsto (fun j => dist (y j) (z j)) atTop (𝓝 0) := by
    have hh : Tendsto (fun j => dist (y j).2 p.2) atTop (𝓝 0) := by
      simpa only [dist_self] using htime.dist (tendsto_const_nhds : Tendsto (fun _ : ℕ => p.2) atTop (𝓝 p.2))
    simpa only [z,Prod.dist_eq,dist_self,max_eq_right dist_nonneg] using hh
  have hwUniform := hK.uniformContinuousOn_of_continuous hw
  have hwdiff : Tendsto (fun j => w (y j)-w (z j)) atTop (𝓝 0) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    obtain ⟨delta,hdelta,hclose⟩ := Metric.uniformContinuousOn_iff.mp hwUniform eps heps
    filter_upwards [hdt (eventually_lt_nhds hdelta)] with j hj
    have hh := hclose (y j) (hy j) (z j) (hz j) hj
    simpa only [Real.dist_eq,sub_zero] using hh
  have hzt : Tendsto z atTop (𝓝 p) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [hwdiff (eventually_lt_nhds (pow_pos heps 4))] with j hj
    change w (y j)-w (z j)<eps^4 at hj
    by_contra hfail
    have hh := pow_le_pow_left₀ heps.le (le_of_not_gt hfail) 4
    have hs := hslice (z j) (hz j) rfl
    linarith only [hh,hs,hwpos j,hj]
  have hyt : Tendsto y atTop (𝓝 p) := by
    apply Metric.tendsto_nhds.mpr
    intro eps heps
    filter_upwards [hdt (eventually_lt_nhds (by positivity : 0<eps/2)),
      hzt (Metric.ball_mem_nhds p (by positivity : 0<eps/2))] with j hj1 hj2
    change dist (y j) (z j)<eps/2 at hj1
    change dist (z j) p<eps/2 at hj2
    have hh := dist_triangle (y j) (z j) p
    linarith only [hh,hj1,hj2]
  exact ⟨y,hy,hyt,hmax⟩

/-- Freeze time only after its genuine derivative has been established. This
is the upper spatial viscosity test, proved by actual space-time contacts. -/
theorem auto_spatial_slice_sub {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ}
    {u V : Point n → ℝ} (hQ : IsOpen Q) (hF : Continuous F)
    (hu : ContinuousOn u Q) (hV : ContinuousOn V Q)
    (hTime : ∀ q∈Q, HasDerivAt (fun t => u (q.1,t)) (V q) q.2)
    (hsub : viscositySub Q (fun H _ => F H) (fun _ => 0) u)
    {p : Point n} (hp : p∈Q) {psi : Space n → ℝ}
    (hpsi : ContDiffAt ℝ 2 psi p.1)
    (ht : psi p.1=u p ∧ ∀ᶠ x in 𝓝 p.1, u (x,p.2)≤psi x) :
    V p≤F (hessian (fun q : Point n => psi q.1) p) := by
  let base : Point n → ℝ := fun q => psi q.1+perronQuartic p q
  have hpsip : ContDiffAt ℝ 2 (fun q : Point n => psi q.1) p := hpsi.comp p contDiffAt_fst
  have hquart : ContDiffAt ℝ 2 (perronQuartic p) p := (perronQuartic_smooth p).contDiffAt.of_le (by simp)
  have hbase : ContDiffAt ℝ 2 base p := hpsip.add hquart
  obtain ⟨O,hOo,hpO,hO2,hTcont,hHcont⟩ := perron_local_c2_jets hbase
  have hgood : ∀ᶠ q in 𝓝 p, q∈Q ∧ q∈O ∧ u (q.1,p.2)≤psi q.1 := by
    filter_upwards [hQ.mem_nhds hp,hOo.mem_nhds hpO,(continuous_fst.tendsto p) ht.2] with q hqQ hqO hqx
    exact ⟨hqQ,hqO,hqx⟩
  obtain ⟨R,hR,hball⟩ := Metric.mem_nhds_iff.mp hgood
  let r := R/2
  have hr : 0<r := by dsimp only [r]; positivity
  let K := Metric.closedBall p r
  have hKgood (q : Point n) (hq : q∈K) : q∈Q ∧ q∈O ∧ u (q.1,p.2)≤psi q.1 :=
    hball (Metric.closedBall_subset_ball (by dsimp only [r]; linarith only [hR]) hq)
  let w : Point n → ℝ := fun q => u q-base q-V p*(q.2-p.2)
  have hw : ContinuousOn w K :=
    ((hu.mono fun q hq => (hKgood q hq).1).sub
      (fun q hq => (hO2 q (hKgood q hq).2.1).continuousAt.continuousWithinAt)).sub
      (continuousOn_const.mul (continuous_snd.continuousOn.sub continuousOn_const))
  have hw0 : w p=0 := by
    simp only [w,base,perronQuartic_center,ht.1,sub_self,mul_zero,add_zero,sub_zero]
  have hwSlice (q : Point n) (hq : q∈K) (htq : q.2=p.2) : w q≤-(dist q p)^4 := by
    rcases q with ⟨x,t⟩
    change t=p.2 at htq
    subst t
    have hh := (hKgood (x,p.2) hq).2.2
    have hdist := perronQuartic_distance p (x,p.2)
    dsimp only [w,base]
    simp only [sub_self,mul_zero,sub_zero]
    linarith only [hh,hdist]
  obtain ⟨y,hy,hyt,hmax⟩ := auto_time_penalty_contacts p hr hw hw0 hwSlice
  let m : ℕ → ℝ := fun j => w (y j)-((j:ℝ)+1)*((y j).2-p.2)^2
  let g : ℕ → ℝ → ℝ := fun j t => V p*(t-p.2)+((j:ℝ)+1)*(t-p.2)^2
  let phi : ℕ → Point n → ℝ := fun j q => base q+g j q.2+m j
  have hyBall : ∀ᶠ j in atTop, y j∈Metric.ball p r :=
    hyt (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr))
  have hineq : ∀ᶠ j in atTop, V (y j)≤F (hessian base (y j)) := by
    filter_upwards [hyBall] with j hj
    have htouch : touchAbove (phi j) u (y j) := by
      refine ⟨?_,?_⟩
      · dsimp only [phi,g,m,w]
        ring
      have hnear : K∈𝓝 (y j) := Metric.closedBall_mem_nhds_of_mem hj
      filter_upwards [hnear] with q hq
      have hh := hmax j hq
      change w q-((j:ℝ)+1)*(q.2-p.2)^2≤ m j at hh
      dsimp only [w] at hh
      change u q≤base q+(V p*(q.2-p.2)+((j:ℝ)+1)*(q.2-p.2)^2)+m j
      linarith only [hh]
    have hpoly : ContDiff ℝ ∞ (fun q : Point n => g j q.2) :=
      (contDiff_const.mul (contDiff_snd.sub contDiff_const)).add
        (contDiff_const.mul ((contDiff_snd.sub contDiff_const).pow 2))
    have hc : ContDiffAt ℝ 2 (phi j) (y j) :=
      ((hO2 (y j) (hKgood (y j) (hy j)).2.1).add
        (hpoly.contDiffAt.of_le (by simp))).add contDiffAt_const
    have hh := auto_sub_at_time_differentiable_contact hsub (hKgood (y j) (hy j)).1
      (hTime (y j) (hKgood (y j) (hy j)).1) hc htouch
    have hH : hessian (phi j) (y j)=hessian base (y j) := by
      dsimp only [phi]
      rw [harnack_hessian_add_const,auto_hessian_add_time]
    rwa [hH] at hh
  have hyQ : Tendsto y atTop (𝓝[Q] p) := tendsto_nhdsWithin_iff.mpr
    ⟨hyt,Filter.Eventually.of_forall fun j => (hKgood (y j) (hy j)).1⟩
  have hyO : Tendsto y atTop (𝓝[O] p) := tendsto_nhdsWithin_iff.mpr
    ⟨hyt,Filter.Eventually.of_forall fun j => (hKgood (y j) (hy j)).2.1⟩
  have hres : V p≤F (hessian base p) := le_of_tendsto_of_tendsto
    ((hV p hp).tendsto.comp hyQ) ((hF.tendsto _).comp ((hHcont p hpO).tendsto.comp hyO)) hineq
  dsimp only [base] at hres
  rwa [perron_hessian_add hpsip hquart,perronQuartic_hessian_zero,add_zero] at hres

theorem auto_spatial_slice_super {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ}
    {u V : Point n → ℝ} (hQ : IsOpen Q) (hF : Continuous F)
    (hu : ContinuousOn u Q) (hV : ContinuousOn V Q)
    (hTime : ∀ q∈Q, HasDerivAt (fun t => u (q.1,t)) (V q) q.2)
    (hsuper : viscositySuper Q (fun H _ => F H) (fun _ => 0) u)
    {p : Point n} (hp : p∈Q) {psi : Space n → ℝ}
    (hpsi : ContDiffAt ℝ 2 psi p.1)
    (ht : psi p.1=u p ∧ ∀ᶠ x in 𝓝 p.1, psi x≤u (x,p.2)) :
    F (hessian (fun q : Point n => psi q.1) p)≤V p := by
  have htouch : (-psi p.1)=(-u p) ∧ ∀ᶠ x in 𝓝 p.1, -u (x,p.2)≤-psi x := by
    refine ⟨congrArg Neg.neg ht.1,?_⟩
    filter_upwards [ht.2] with x hx
    exact neg_le_neg hx
  have hh := auto_spatial_slice_sub hQ (hF.comp continuous_neg).neg hu.neg hV.neg
    (fun q hq => (hTime q hq).neg) (auto_super_iff_neg_sub.mp hsuper) hp hpsi.neg htouch
  change -V p≤-F (-hessian (fun q : Point n => -psi q.1) p) at hh
  have hj := (auto_negate_test_jets (hpsi.comp p contDiffAt_fst)).2
  simp only [Function.comp_def] at hj
  rw [hj,neg_neg] at hh
  linarith only [hh]

/-- Spatial smoothness and genuine C¹ time suffice for the pointwise residual.
The function u need not be a joint C² test. -/
theorem auto_actual_residual_sub {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ}
    {u V : Point n → ℝ} (hQ : IsOpen Q) (hF : Continuous F)
    (hu : ContinuousOn u Q) (hV : ContinuousOn V Q)
    (hTime : ∀ q∈Q, HasDerivAt (fun t => u (q.1,t)) (V q) q.2)
    (hsub : viscositySub Q (fun H _ => F H) (fun _ => 0) u)
    {p : Point n} (hp : p∈Q) (hspace : ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1) :
    V p≤F (hessian u p) := by
  have hh := auto_spatial_slice_sub hQ hF hu hV hTime hsub hp hspace
    ⟨by rw [Prod.eta],Filter.Eventually.of_forall fun _ => le_rfl⟩
  exact hh

theorem auto_actual_residual_super {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ}
    {u V : Point n → ℝ} (hQ : IsOpen Q) (hF : Continuous F)
    (hu : ContinuousOn u Q) (hV : ContinuousOn V Q)
    (hTime : ∀ q∈Q, HasDerivAt (fun t => u (q.1,t)) (V q) q.2)
    (hsuper : viscositySuper Q (fun H _ => F H) (fun _ => 0) u)
    {p : Point n} (hp : p∈Q) (hspace : ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1) :
    F (hessian u p)≤V p := by
  have hh := auto_spatial_slice_super hQ hF hu hV hTime hsuper hp hspace
    ⟨by rw [Prod.eta],Filter.Eventually.of_forall fun _ => le_rfl⟩
  exact hh

theorem auto_actual_residual_eq {n : ℕ} {Q : Set (Point n)} {F : Sym n → ℝ}
    {u V : Point n → ℝ} (hQ : IsOpen Q) (hF : Continuous F)
    (hu : ContinuousOn u Q) (hV : ContinuousOn V Q)
    (hTime : ∀ q∈Q, HasDerivAt (fun t => u (q.1,t)) (V q) q.2)
    (hsol : viscositySolution Q (fun H _ => F H) (fun _ => 0) u)
    {p : Point n} (hp : p∈Q) (hspace : ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1) :
    V p=F (hessian u p) :=
  le_antisymm (auto_actual_residual_sub hQ hF hu hV hTime hsol.1 hp hspace)
    (auto_actual_residual_super hQ hF hu hV hTime hsol.2 hp hspace)

end Yau.LeafProofs.L05AutonomousAux
