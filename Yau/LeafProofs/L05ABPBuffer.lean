import Yau.LeafProofs.L05ABPQuadraticContact
import Yau.LeafProofs.L05ABPRetraction
import Yau.LeafProofs.L05ABPSemiconvexABP

noncomputable section

open Filter MeasureTheory Asymptotics
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic

theorem abp_buffer_subset {n : ℕ} {rho : ℝ} (hrho : 0<rho) (hsmall : rho<1/4) :
    abpClosed n (1-rho) (-1+rho) (-rho)⊆unitClosed n := by
  intro z hz
  have hx : ‖z.1‖≤1-rho := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
  refine ⟨?_,?_,?_⟩
  · simpa only [Metric.mem_closedBall,dist_zero_right] using (show ‖z.1‖≤1 by linarith)
  · exact (show (-1:ℝ)≤-1+rho by linarith).trans hz.2.1
  · exact hz.2.2.trans (by linarith)

theorem abp_buffer_near_mem {n : ℕ} {rho : ℝ} (hrho : 0<rho) (hsmall : rho<1/4)
    {z q : Point n} (hz : z∈abpClosed n (1-rho) (-1+rho) (-rho)) (hq : dist q z<rho) :
    q∈unitOpen n := by
  have hnorm : ‖q-z‖<rho := by simpa only [dist_eq_norm] using hq
  have hx : ‖z.1‖≤1-rho := by simpa only [Metric.mem_closedBall,dist_zero_right] using hz.1
  have hdx : ‖q.1-z.1‖<rho := (show ‖q.1-z.1‖≤‖q-z‖ from norm_fst_le (q-z)).trans_lt hnorm
  have hdt : |q.2-z.2|<rho := (show |q.2-z.2|≤‖q-z‖ from norm_snd_le (q-z)).trans_lt hnorm
  have hqx : ‖q.1‖≤‖q.1-z.1‖+‖z.1‖ := by
    simpa only [sub_zero] using norm_sub_le_norm_sub_add_norm_sub q.1 z.1 (0 : Space n)
  refine ⟨?_,?_,?_⟩
  · simpa only [Metric.mem_ball,dist_zero_right] using (show ‖q.1‖<1 by linarith)
  · linarith [(abs_lt.mp hdt).1,hz.2.1]
  · linarith [(abs_lt.mp hdt).2,hz.2.2]

theorem unitOpen_subset_unitClosed {n : ℕ} : unitOpen n⊆unitClosed n :=
  fun _ hz => ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩

theorem abp_buffer_boundary_near {n : ℕ} {rho : ℝ} (hrho : 0<rho) (hsmall : rho<1/4)
    {z : Point n} (hz : z∈abpBoundary n (1-rho) (-1+rho) (-rho)) :
    ∃ q∈parabolicBoundary n, q∈unitClosed n ∧ dist z q≤rho := by
  have hR : 0<1-rho := by linarith
  rcases hz with hz | hz
  · have ht : z.2=-1+rho := hz.2
    refine ⟨(z.1,-1),Or.inl ⟨?_,rfl⟩,?_,?_⟩
    · exact (abp_buffer_subset hrho hsmall ⟨hz.1,by rw [ht]; constructor <;> linarith⟩).1
    · refine ⟨?_,by norm_num⟩
      exact (abp_buffer_subset hrho hsmall ⟨hz.1,by rw [ht]; constructor <;> linarith⟩).1
    · rw [dist_eq_norm]
      simp only [Prod.sub_def,sub_self,Prod.norm_mk,norm_zero,Real.norm_eq_abs,ht]
      have he : -1+rho-(-1)=rho := by ring
      rw [he,abs_of_pos hrho,max_eq_right hrho.le]
  · have hx : ‖z.1‖=1-rho := by simpa only [Metric.mem_sphere,dist_zero_right] using hz.1
    let q : Point n := ((1-rho)⁻¹ • z.1,z.2)
    have hqx : ‖q.1‖=1 := by
      dsimp only [q]
      rw [norm_smul,Real.norm_eq_abs,abs_of_pos (inv_pos.mpr hR),hx,inv_mul_cancel₀ hR.ne']
    have hqD : q∈unitClosed n := by
      refine ⟨?_,?_,?_⟩
      · simpa only [Metric.mem_closedBall,dist_zero_right] using hqx.le
      · exact (show (-1:ℝ)≤-1+rho by linarith).trans hz.2.1
      · exact hz.2.2.trans (by linarith)
    refine ⟨q,Or.inr ⟨?_,hqD.2⟩,hqD,?_⟩
    · simpa only [Metric.mem_sphere,dist_zero_right] using hqx
    · rw [dist_eq_norm]
      have he : z-q=((1-(1-rho)⁻¹) • z.1,0) := by
        apply Prod.ext
        · change z.1-(1-rho)⁻¹ • z.1=(1-(1-rho)⁻¹) • z.1
          module
        · exact sub_self _
      rw [he,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _),norm_smul,
        Real.norm_eq_abs,hx]
      have hcoef : 1-(1-rho)⁻¹= -rho/(1-rho) := by field_simp; ring
      rw [hcoef,abs_div,abs_neg,abs_of_pos hrho,abs_of_pos hR,div_mul_cancel₀ _ hR.ne']

theorem lasryLions_buffer_contact_inequality {n : ℕ}
    {f v g : Point n → ℝ} {M epsilon ell L rho s : ℝ}
    (hf : Continuous f) (hM : 0≤M) (hb : ∀ q, |f q|≤M)
    (hepsilon : 0<epsilon) (hell : 0<ell) (hL : ell≤L)
    (hrho : 0<rho) (hsmall : rho<1/4) (heps : 64*M*epsilon<rho^2)
    (heq : Set.EqOn f v (unitClosed n))
    (hsub : viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) g v)
    (hmod : ∀ z ∈ unitClosed n, ∀ q ∈ unitClosed n, dist q z < rho → |g q - g z| ≤ s)
    {z : Point n} {xi : Space n} {l : Point n →L[ℝ] ℝ}
    {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (hz : z∈abpOpen n (1-rho) (-1+rho) (-rho))
    (hs : pastSupports (1-rho) (-1+rho)
      (spatialInfRegularize (epsilon/2) (supRegularize epsilon f)) z xi)
    (hjet : jointPeanoJet
      (spatialInfRegularize (epsilon/2) (supRegularize epsilon f)) z l B) :
    l (0,1)+(ell/2)*Matrix.trace (-(jointHessian B : Mat n))≤g z+s := by
  have hU := supRegularize_continuous hf hM hb hepsilon
  have hbU : ∀ q, |supRegularize epsilon f q|≤M :=
    fun q => (supRegularize_bounds hf hM hb hepsilon q).2
  obtain ⟨y,hy,_,hyd⟩ := spatialInfRegularize_attained hU hM hbU (show 0<epsilon/2 by positivity) z
  obtain ⟨q,hq,_,hqd⟩ := supRegularize_attained hf hM hb hepsilon (y,z.2)
  have hzy : dist z (y,z.2)<rho/4 := by
    rw [dist_eq_norm]
    have he : ‖z-(y,z.2)‖=‖z.1-y‖ := by
      simp only [Prod.sub_def,sub_self,Prod.norm_mk,norm_zero,max_eq_left (norm_nonneg _)]
    rw [he]
    nlinarith [norm_nonneg (z.1-y)]
  have hyq : dist (y,z.2) q<rho/4 := by
    rw [dist_eq_norm]
    have hh := norm_sq_le_qnorm2 ((y,z.2)-q)
    nlinarith [norm_nonneg (((y,z.2) : Point n)-q)]
  have hdist : dist q z<rho := by
    have hh := dist_triangle q (y,z.2) z
    rw [dist_comm q (y,z.2),dist_comm (y,z.2) z] at hh
    linarith
  have hzD : z∈abpClosed n (1-rho) (-1+rho) (-rho) :=
    ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩
  have hqQ := abp_buffer_near_mem hrho hsmall hzD hdist
  have hi := lasryLions_peano_contact_inequality hf hM hb hepsilon hell hL
    (Metric.isOpen_ball.prod isOpen_Ioo) (heq.mono unitOpen_subset_unitClosed)
    hsub hz hs hjet hy hqQ hq
  have hg := (abs_le.mp (hmod z (abp_buffer_subset hrho hsmall hzD) q
    (unitOpen_subset_unitClosed hqQ) hdist)).2
  linarith

theorem jointSemiconvex_sub_const {n : ℕ} {w : Point n → ℝ} {K : ℝ}
    (hw : jointSemiconvex K w) (c : ℝ) : jointSemiconvex K (fun q => w q-c) := by
  unfold jointSemiconvex at hw ⊢
  convert! hw.add_const (-c) using 1
  funext q
  simp only [Pi.add_apply]
  ring

theorem jointPeanoJet_add_const {n : ℕ} {w : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ}
    (h : jointPeanoJet w z l B) (c : ℝ) : jointPeanoJet (fun q => w q+c) z l B := by
  refine ⟨h.1,h.2.congr_left ?_⟩
  intro q
  ring

theorem jointPeanoJet_of_sub_const {n : ℕ} {w : Point n → ℝ} {z : Point n}
    {l : Point n →L[ℝ] ℝ} {B : Point n →L[ℝ] Point n →L[ℝ] ℝ} {c : ℝ}
    (h : jointPeanoJet (fun q => w q-c) z l B) : jointPeanoJet w z l B := by
  simpa only [sub_add_cancel] using jointPeanoJet_add_const h c

theorem lasryLions_buffer_abp_power {n : ℕ}
    {f v g : Point n → ℝ} {M epsilon ell L rho eta : ℝ}
    (hf : Continuous f) (hM : 0≤M) (hb : ∀ q, |f q|≤M)
    (hepsilon : 0<epsilon) (hell : 0<ell) (hL : ell≤L)
    (hrho : 0<rho) (hsmall : rho<1/4) (heps : 64*M*epsilon<rho^2)
    (heta : 0≤eta) (heq : Set.EqOn f v (unitClosed n))
    (hg : ContinuousOn g (unitClosed n))
    (hboundary : ∀ z∈parabolicBoundary n, v z≤0)
    (hsub : viscositySub (unitOpen n) (fun H _ => pucciPlus ell L H) g v)
    (hmodv : ∀ z∈unitClosed n, ∀ q∈unitClosed n, dist z q≤rho → |v z-v q|≤eta)
    (hmodg : ∀ z∈unitClosed n, ∀ q∈unitClosed n, dist q z<rho → |g q-g z|≤eta)
    (happrox : ∀ z∈unitClosed n,
      |spatialInfRegularize (epsilon/2) (supRegularize epsilon f) z-v z|≤eta)
    {z0 : Point n} (hz0 : z0∈abpClosed n (1-rho) (-1+rho) (-rho)) :
    abpKappa n*(max (spatialInfRegularize (epsilon/2) (supRegularize epsilon f) z0-2*eta) 0)^(2*n+1)≤
      ((ell/2)⁻¹)^(2*n)*∫ z in unitOpen n, (max (g z+eta) 0)^(2*n+1) := by
  let W := spatialInfRegularize (epsilon/2) (supRegularize epsilon f)
  let w := fun q => W q-2*eta
  have hsemi := (lasryLions_semiconvex_semiconcave hf hM hb hepsilon).1
  have hbW := (lasryLions_semiconvex_semiconcave hf hM hb hepsilon).2.2
  have hw : Continuous w := (jointSemiconvex_locallyLipschitz hsemi).continuous.sub continuous_const
  have hbw : ∀ z, |w z|≤M+|2*eta| := by
    intro z
    exact (abs_sub (W z) (2*eta)).trans (add_le_add (hbW z) le_rfl)
  have hbd : ∀ z∈abpBoundary n (1-rho) (-1+rho) (-rho), w z≤0 := by
    intro z hz
    obtain ⟨q,hqb,hqD,hdist⟩ := abp_buffer_boundary_near hrho hsmall hz
    have hzD : z∈unitClosed n := by
      apply abp_buffer_subset hrho hsmall
      rcases hz with hz | hz
      · exact ⟨hz.1,by rw [show z.2=-1+rho from hz.2]; constructor <;> linarith⟩
      · exact ⟨Metric.sphere_subset_closedBall hz.1,hz.2⟩
    have hv := (abs_le.mp (hmodv z hzD q hqD hdist)).2
    have he := (abs_le.mp (happrox z hzD)).2
    have hqv := hboundary q hqb
    dsimp only [w]
    linarith
  have hsrc : ∀ᵐ z ∂(volume.restrict (abpOpen n (1-rho) (-1+rho) (-rho))),
      ∀ (l : Point n →L[ℝ] ℝ) (B : Point n →L[ℝ] Point n →L[ℝ] ℝ),
        jointPeanoJet w z l B → pastSupports (1-rho) (-1+rho) w z (spatialGrad w z) →
          l (0,1)+(ell/2)*Matrix.trace (-(jointHessian B : Mat n))≤g z+eta := by
    filter_upwards [ae_restrict_mem (Metric.isOpen_ball.prod isOpen_Ioo).measurableSet] with z hz
    intro l B hjet hs
    have hP : jointPeanoJet W z l B := jointPeanoJet_of_sub_const hjet
    have hs' : pastSupports (1-rho) (-1+rho) W z (spatialGrad w z) :=
      (pastSupports_sub_const W (2*eta) z (spatialGrad w z)).mp hs
    exact lasryLions_buffer_contact_inequality hf hM hb hepsilon hell hL hrho hsmall heps
      heq hsub hmodg hz hs' hP
  have hg' : ContinuousOn (fun z => g z+eta) (abpClosed n (1-rho) (-1+rho) (-rho)) :=
    (hg.add continuousOn_const).mono (abp_buffer_subset hrho hsmall)
  have hi := semiconvex_contact_abp_power (show 0<1-rho by linarith)
    (show 1-rho≤1 by linarith) (show -1+rho< -rho by linarith)
    (show 0<ell/2 by positivity) hw (jointSemiconvex_sub_const hsemi (2*eta))
    (show 0≤2/epsilon by positivity) (show 0≤M+|2*eta| by positivity) hbw hg' hbd hsrc hz0
  have hD : IsCompact (unitClosed n) := (isCompact_closedBall (0 : Space n) 1).prod isCompact_Icc
  have hint : IntegrableOn (fun z => (max (g z+eta) 0)^(2*n+1)) (unitOpen n) :=
    (((hg.add continuousOn_const).sup continuousOn_const).pow _).integrableOn_compact hD |>.mono_set unitOpen_subset_unitClosed
  have hQsub : abpOpen n (1-rho) (-1+rho) (-rho)⊆unitOpen n := by
    intro z hz
    apply abp_buffer_near_mem hrho hsmall
      ⟨Metric.ball_subset_closedBall hz.1,hz.2.1.le,hz.2.2.le⟩
    simpa only [dist_self] using hrho
  have hintle := setIntegral_mono_set hint
    (Filter.Eventually.of_forall (fun z => pow_nonneg (le_max_right (g z+eta) 0) _))
    (Filter.Eventually.of_forall hQsub)
  exact hi.trans (mul_le_mul_of_nonneg_left hintle (pow_nonneg (inv_nonneg.mpr (by positivity : 0≤ell/2)) _))

end Yau.LeafProofs.L05Aux
