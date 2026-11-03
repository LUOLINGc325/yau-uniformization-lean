import Yau.LeafProofs.L05PerronClassical

noncomputable section
set_option maxHeartbeats 1200000

open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem perron_upper_touch_translate_eventual {E : Type*} [NormedAddCommGroup E]
    {u U phi : E → ℝ} {z q : E} {c : ℝ} (ha : U z=u q-c)
    (hc : ∀ᶠ r in 𝓝 q, u r-c≤U (r+(z-q)))
    (ht : phi z=U z ∧ ∀ᶠ r in 𝓝 z, U r≤phi r) :
    (phi (q+(z-q))+c=u q) ∧ ∀ᶠ r in 𝓝 q, u r≤phi (r+(z-q))+c := by
  have hqz : q+(z-q)=z := by abel
  have hmap : Tendsto (fun r : E => r+(z-q)) (𝓝 q) (𝓝 z) := by
    have hcont : Continuous (fun r : E => r+(z-q)) := continuous_id.add continuous_const
    simpa only [hqz] using hcont.tendsto q
  refine ⟨?_,?_⟩
  · rw [hqz,ht.1,ha]
    exact sub_add_cancel _ _
  · filter_upwards [hc,hmap ht.2] with r hr hrt
    exact (sub_le_iff_le_add).mp (hr.trans hrt)

theorem perron_lower_touch_translate_eventual {E : Type*} [NormedAddCommGroup E]
    {u U phi : E → ℝ} {z q : E} {c : ℝ} (ha : U z=u q+c)
    (hc : ∀ᶠ r in 𝓝 q, U (r+(z-q))≤u r+c)
    (ht : phi z=U z ∧ ∀ᶠ r in 𝓝 z, phi r≤U r) :
    (phi (q+(z-q))-c=u q) ∧ ∀ᶠ r in 𝓝 q, phi (r+(z-q))-c≤u r := by
  have hqz : q+(z-q)=z := by abel
  have hmap : Tendsto (fun r : E => r+(z-q)) (𝓝 q) (𝓝 z) := by
    have hcont : Continuous (fun r : E => r+(z-q)) := continuous_id.add continuous_const
    simpa only [hqz] using hcont.tendsto q
  refine ⟨?_,?_⟩
  · rw [hqz,ht.1,ha]
    exact add_sub_cancel_right _ _
  · filter_upwards [hc,hmap ht.2] with r hr hrt
    exact (sub_le_iff_le_add).mpr (hrt.trans hr)

def perronSupConv {n : ℕ} (K : Set (Point n)) (eps : ℝ)
    (u : Point n → ℝ) (z : Point n) : ℝ :=
  sSup {r | ∃ q∈K, r=u q-qnorm2 (z-q)/(2*eps)}

def perronInfConv {n : ℕ} (K : Set (Point n)) (eps : ℝ)
    (v : Point n → ℝ) (z : Point n) : ℝ :=
  -perronSupConv K eps (fun q => -v q) z

theorem perron_supConv_attained {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) (eps : ℝ) (z : Point n) :
    ∃ q∈K, perronSupConv K eps u z=u q-qnorm2 (z-q)/(2*eps) := by
  have hc : Continuous (fun q : Point n => -(qnorm2 (z-q)/(2*eps))) := by
    exact ((qnorm2_continuous.comp (continuous_const.sub continuous_id)).div_const _).neg
  have hs : UpperSemicontinuousOn (fun q => u q-qnorm2 (z-q)/(2*eps)) K := by
    simpa only [sub_eq_add_neg] using hu.add hc.continuousOn.upperSemicontinuousOn
  obtain ⟨q,hq,hmax⟩ := hs.exists_isMaxOn hne hK
  have hnon : ({r | ∃ q∈K, r=u q-qnorm2 (z-q)/(2*eps)} : Set ℝ).Nonempty :=
    ⟨u q-qnorm2 (z-q)/(2*eps),q,hq,rfl⟩
  have hb : BddAbove {r | ∃ q∈K, r=u q-qnorm2 (z-q)/(2*eps)} := by
    refine ⟨u q-qnorm2 (z-q)/(2*eps),?_⟩
    rintro r ⟨r',hr',rfl⟩
    exact hmax hr'
  refine ⟨q,hq,le_antisymm ?_ ?_⟩
  · exact csSup_le hnon (by rintro r ⟨r',hr',rfl⟩; exact hmax hr')
  · exact le_csSup hb ⟨q,hq,rfl⟩

theorem le_perronSupConv {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) (eps : ℝ) (z : Point n) {q : Point n} (hq : q∈K) :
    u q-qnorm2 (z-q)/(2*eps)≤perronSupConv K eps u z := by
  obtain ⟨r,hr,he⟩ := perron_supConv_attained hne hK hu eps z
  have hc : Continuous (fun q : Point n => -(qnorm2 (z-q)/(2*eps))) := by
    exact ((qnorm2_continuous.comp (continuous_const.sub continuous_id)).div_const _).neg
  have hs : UpperSemicontinuousOn (fun q => u q-qnorm2 (z-q)/(2*eps)) K := by
    simpa only [sub_eq_add_neg] using hu.add hc.continuousOn.upperSemicontinuousOn
  have hb : BddAbove {r | ∃ q∈K, r=u q-qnorm2 (z-q)/(2*eps)} := by
    obtain ⟨C,hC⟩ := hs.bddAbove_of_isCompact hK
    refine ⟨C,?_⟩
    rintro r ⟨q,hq,rfl⟩
    exact hC (Set.mem_image_of_mem _ hq)
  exact le_csSup hb ⟨q,hq,rfl⟩

theorem perron_supConv_upper {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) {M eps : ℝ}
    (hb : ∀ q∈K, |u q|≤M) (he : 0<eps) (z : Point n) : perronSupConv K eps u z≤M := by
  obtain ⟨q,hq,ha⟩ := perron_supConv_attained hne hK hu eps z
  rw [ha]
  exact (sub_le_self _ (div_nonneg (qnorm2_nonneg _) (by positivity))).trans (abs_le.mp (hb q hq)).2

theorem perron_supConv_diagonal {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) (eps : ℝ) {z : Point n} (hz : z∈K) :
    u z≤perronSupConv K eps u z := by
  simpa [qnorm2] using le_perronSupConv hne hK hu eps z hz

theorem perron_supConv_displacement {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) {M eps : ℝ}
    (hb : ∀ q∈K, |u q|≤M) (he : 0<eps) {z q : Point n} (hz : z∈K) (hq : q∈K)
    (ha : perronSupConv K eps u z=u q-qnorm2 (z-q)/(2*eps)) :
    qnorm2 (z-q)≤4*M*eps := by
  have hlo := perron_supConv_diagonal hne hK hu eps hz
  rw [ha] at hlo
  have hzlo := (abs_le.mp (hb z hz)).1
  have hqhi := (abs_le.mp (hb q hq)).2
  have hcost : qnorm2 (z-q)/(2*eps)≤2*M := by linarith
  have hh := (div_le_iff₀ (by positivity : 0<2*eps)).mp hcost
  nlinarith

theorem perron_supConv_semiconvex {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) (eps : ℝ) :
    ConvexOn ℝ Set.univ (fun z => perronSupConv K eps u z+qnorm2 z/(2*eps)) := by
  refine ⟨convex_univ,?_⟩
  intro z _ w _ a b ha hb hab
  obtain ⟨q,hq,he⟩ := perron_supConv_attained hne hK hu eps (a • z+b • w)
  have hz := mul_le_mul_of_nonneg_left (le_perronSupConv hne hK hu eps z hq) ha
  have hw := mul_le_mul_of_nonneg_left (le_perronSupConv hne hK hu eps w hq) hb
  have hquad := qnorm2_difference_affine z w q hab
  have hvsum : u q=a*u q+b*u q := by rw [←add_mul,hab,one_mul]
  simp only [smul_eq_mul]
  rw [he]
  have hid : u q-qnorm2 (a • z+b • w-q)/(2*eps)+qnorm2 (a • z+b • w)/(2*eps)=
      a*(u q-qnorm2 (z-q)/(2*eps))+b*(u q-qnorm2 (w-q)/(2*eps))+
        a*(qnorm2 z/(2*eps))+b*(qnorm2 w/(2*eps)) := by
    have hh := congrArg (fun r : ℝ => r/(2*eps)) hquad
    simp only [sub_div,add_div,mul_div_assoc] at hh
    nlinarith
  rw [hid]
  linarith

theorem perron_supConv_continuous {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) (eps : ℝ) : Continuous (perronSupConv K eps u) := by
  have hc := continuousOn_univ.mp ((perron_supConv_semiconvex hne hK hu eps).continuousOn isOpen_univ)
  apply (hc.sub (qnorm2_continuous.div_const (2*eps))).congr
  intro z
  change (perronSupConv K eps u z+qnorm2 z/(2*eps))-qnorm2 z/(2*eps)=perronSupConv K eps u z
  ring

theorem perron_supConv_touch {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u : Point n → ℝ}
    (hu : UpperSemicontinuousOn u K) (eps : ℝ)
    {z q : Point n} (hq : q∈interior K)
    (ha : perronSupConv K eps u z=u q-qnorm2 (z-q)/(2*eps))
    {phi : Point n → ℝ} (ht : touchAbove phi (perronSupConv K eps u) z) :
    touchAbove (fun r => phi (r+(z-q))+qnorm2 (z-q)/(2*eps)) u q := by
  apply perron_upper_touch_translate_eventual ha _ ht
  filter_upwards [mem_interior_iff_mem_nhds.mp hq] with r hr
  have hc := le_perronSupConv hne hK hu eps (r+(z-q)) hr
  rw [show r+(z-q)-r=z-q by abel] at hc
  exact hc

theorem perron_infConv_attained {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {v : Point n → ℝ}
    (hv : LowerSemicontinuousOn v K) (eps : ℝ) (z : Point n) :
    ∃ q∈K, perronInfConv K eps v z=v q+qnorm2 (z-q)/(2*eps) := by
  obtain ⟨q,hq,ha⟩ := perron_supConv_attained hne hK hv.neg eps z
  refine ⟨q,hq,?_⟩
  change perronSupConv K eps (fun q => -v q) z= -v q-qnorm2 (z-q)/(2*eps) at ha
  rw [perronInfConv,ha]
  ring

theorem perron_infConv_continuous {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {v : Point n → ℝ}
    (hv : LowerSemicontinuousOn v K) (eps : ℝ) : Continuous (perronInfConv K eps v) :=
  (perron_supConv_continuous hne hK hv.neg eps).neg

theorem perron_infConv_le_candidate {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {v : Point n → ℝ}
    (hv : LowerSemicontinuousOn v K) (eps : ℝ) (z : Point n) {q : Point n} (hq : q∈K) :
    perronInfConv K eps v z≤v q+qnorm2 (z-q)/(2*eps) := by
  have hh := le_perronSupConv hne hK hv.neg eps z hq
  change -v q-qnorm2 (z-q)/(2*eps)≤perronSupConv K eps (fun q => -v q) z at hh
  dsimp only [perronInfConv]
  linarith

theorem perron_infConv_diagonal {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {v : Point n → ℝ}
    (hv : LowerSemicontinuousOn v K) (eps : ℝ) {z : Point n} (hz : z∈K) :
    perronInfConv K eps v z≤v z := by
  simpa [qnorm2] using perron_infConv_le_candidate hne hK hv eps z hz

theorem perron_infConv_touch {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {v : Point n → ℝ}
    (hv : LowerSemicontinuousOn v K) (eps : ℝ)
    {z q : Point n} (hq : q∈interior K)
    (ha : perronInfConv K eps v z=v q+qnorm2 (z-q)/(2*eps))
    {phi : Point n → ℝ} (ht : touchBelow phi (perronInfConv K eps v) z) :
    touchBelow (fun r => phi (r+(z-q))-qnorm2 (z-q)/(2*eps)) v q := by
  apply perron_lower_touch_translate_eventual ha _ ht
  filter_upwards [mem_interior_iff_mem_nhds.mp hq] with r hr
  have hc := perron_infConv_le_candidate hne hK hv eps (r+(z-q)) hr
  rw [show r+(z-q)-r=z-q by abel] at hc
  exact hc

theorem perron_infConv_lower {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {v : Point n → ℝ}
    (hv : LowerSemicontinuousOn v K) {M eps : ℝ}
    (hb : ∀ q∈K, |v q|≤M) (he : 0<eps) (z : Point n) : -M≤perronInfConv K eps v z := by
  have hneg : UpperSemicontinuousOn (fun q => -v q) K := hv.neg
  have hbneg : ∀ q∈K, |-v q|≤M := fun q hq => by simpa only [abs_neg] using hb q hq
  exact neg_le_neg (perron_supConv_upper hne hK hneg hbneg he z)

theorem perron_infConv_displacement {n : ℕ} {K : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {v : Point n → ℝ}
    (hv : LowerSemicontinuousOn v K) {M eps : ℝ}
    (hb : ∀ q∈K, |v q|≤M) (he : 0<eps) {z q : Point n} (hz : z∈K) (hq : q∈K)
    (ha : perronInfConv K eps v z=v q+qnorm2 (z-q)/(2*eps)) :
    qnorm2 (z-q)≤4*M*eps := by
  have hneg : UpperSemicontinuousOn (fun q => -v q) K := hv.neg
  have hbneg : ∀ q∈K, |-v q|≤M := fun q hq => by simpa only [abs_neg] using hb q hq
  have ha' : perronSupConv K eps (fun q => -v q) z= -v q-qnorm2 (z-q)/(2*eps) := by
    dsimp only [perronInfConv] at ha
    linarith
  exact perron_supConv_displacement hne hK hneg hbneg he hz hq ha'

theorem perron_supConv_viscosity_jet {n : ℕ} {K Q : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {u phi g : Point n → ℝ}
    {G : Sym n → Point n → ℝ} (hu : UpperSemicontinuousOn u K) (eps : ℝ)
    (hsub : viscositySub Q G g u) {z q : Point n} (hq : q∈interior K) (hqQ : q∈Q)
    (ha : perronSupConv K eps u z=u q-qnorm2 (z-q)/(2*eps))
    (hphi : ContDiffAt ℝ 2 phi z) (ht : touchAbove phi (perronSupConv K eps u) z) :
    timeD Set.univ phi z-G (hessian phi z) q≤g q := by
  have hqz : q+(z-q)=z := by abel
  have hs : ContDiffAt ℝ 2 (fun r => phi (r+(z-q))+qnorm2 (z-q)/(2*eps)) q := by
    have hc : ContDiffAt ℝ 2 phi (q+(z-q)) := by simpa only [hqz] using hphi
    have hshift : ContDiffAt ℝ 2 (fun r : Point n => r+(z-q)) q := by fun_prop
    exact (hc.comp q hshift).add contDiffAt_const
  have hi := hsub q hqQ _ hs (perron_supConv_touch hne hK hu eps hq ha ht)
  rwa [timeD_translate,hessian_translate,hqz] at hi

theorem perron_infConv_viscosity_jet {n : ℕ} {K Q : Set (Point n)}
    (hne : K.Nonempty) (hK : IsCompact K) {v phi g : Point n → ℝ}
    {G : Sym n → Point n → ℝ} (hv : LowerSemicontinuousOn v K) (eps : ℝ)
    (hsuper : viscositySuper Q G g v) {z q : Point n} (hq : q∈interior K) (hqQ : q∈Q)
    (ha : perronInfConv K eps v z=v q+qnorm2 (z-q)/(2*eps))
    (hphi : ContDiffAt ℝ 2 phi z) (ht : touchBelow phi (perronInfConv K eps v) z) :
    g q≤timeD Set.univ phi z-G (hessian phi z) q := by
  have hqz : q+(z-q)=z := by abel
  have hs : ContDiffAt ℝ 2 (fun r => phi (r+(z-q))+(-qnorm2 (z-q)/(2*eps))) q := by
    have hc : ContDiffAt ℝ 2 phi (q+(z-q)) := by simpa only [hqz] using hphi
    have hshift : ContDiffAt ℝ 2 (fun r : Point n => r+(z-q)) q := by fun_prop
    exact (hc.comp q hshift).add contDiffAt_const
  have ht' : touchBelow (fun r => phi (r+(z-q))+(-qnorm2 (z-q)/(2*eps))) v q := by
    simpa only [neg_div,sub_eq_add_neg] using perron_infConv_touch hne hK hv eps hq ha ht
  have hi := hsuper q hqQ _ hs ht'
  rwa [timeD_translate,hessian_translate,hqz] at hi

end Yau.LeafProofs.L05Aux
