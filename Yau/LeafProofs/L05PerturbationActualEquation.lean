import Yau.LeafProofs.L05PerturbationContact
import Yau.LeafProofs.L05ParabolicClassical

open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_hessian_add_time {n : ℕ} (u : Point n → ℝ) (a : ℝ → ℝ) (p : Point n) :
    hessian (fun q => u q+a q.2) p=hessian u p := by
  have hd : fderiv ℝ (fun x : Space n => u (x,p.2)+a p.2)=
      fderiv ℝ (fun x : Space n => u (x,p.2)) := funext (fun _ => fderiv_add_const _)
  unfold hessian spatialDD
  rw [hd]

theorem perturb_box_in_nhds {n : ℕ} {z : Point n} {U : Set (Point n)}
    (hU : U ∈ 𝓝 z) :
    ∃ r : ℝ, 0<r ∧ closedBall z.1 r ×ˢ Icc (z.2-r) (z.2+r) ⊆ U := by
  obtain ⟨delta,hd,hsub⟩ := Metric.mem_nhds_iff.mp hU
  refine ⟨delta/2,by positivity,?_⟩
  intro p hp
  apply hsub
  have ht : |p.2-z.2|≤delta/2 := abs_le.mpr ⟨by linarith [hp.2.1],by linarith [hp.2.2]⟩
  change dist p z<delta
  rw [Prod.dist_eq,Real.dist_eq]
  exact (max_le hp.1 ht).trans_lt (by linarith)

/-- A true temporal-penalty contact recovers the actual subsolution inequality
without using the parabolic C2 function as a joint C2 test. -/
theorem perturb_actual_sub_open {n : ℕ} {Q : Set (Point n)}
    (hQ : IsOpen Q) {F : Sym n → ℝ} (hF : Continuous F)
    {u : Point n → ℝ} (hu : C2 Q u)
    (hsub : viscositySub Q (fun H _ => F H) (fun _ => 0) u) :
    ∀ z ∈ Q, timeD Q u z≤F (hessian u z) := by
  intro z hz
  by_contra hn
  have hbad : F (hessian u z)<timeD Q u z := lt_of_not_ge hn
  let psi : Point n → ℝ := fun q => u (q.1,z.2)+perronQuartic z q
  have hf : ContDiffAt ℝ 2 (fun q : Point n => u (q.1,z.2)) z :=
    (hu.2.2.2.2.1 z hz).comp z contDiffAt_fst
  have h4 : ContDiffAt ℝ 2 (perronQuartic z) z :=
    (perronQuartic_smooth z).contDiffAt.of_le (by simp)
  have hpsi : ContDiffAt ℝ 2 psi z := hf.add h4
  have hH : hessian psi z=hessian u z := by
    have he : psi=(fun q => u (q.1,z.2)-(-perronQuartic z q)) := by
      funext q
      simp [psi]
    rw [he,perron_hessian_sub hf h4.neg,perron_hessian_neg h4,perronQuartic_hessian_zero]
    simp only [neg_zero,sub_zero]
    rfl
  obtain ⟨V,hV,hzV,hpsiV,_htV,hHV⟩ := perron_local_c2_jets hpsi
  have hut : ContinuousAt (timeD Q u) z := hu.2.2.2.1.continuousAt (hQ.mem_nhds hz)
  have hFV : ContinuousAt (fun q => F (hessian psi q)) z :=
    hF.continuousAt.comp (hHV.continuousAt (hV.mem_nhds hzV))
  have hpos : {q | 0<timeD Q u q-F (hessian psi q)} ∈ 𝓝 z :=
    (hut.sub hFV).preimage_mem_nhds (Ioi_mem_nhds (by change 0<timeD Q u z-F (hessian psi z); rw [hH]; linarith))
  obtain ⟨r,hr,hK⟩ := perturb_box_in_nhds
    (inter_mem (inter_mem (hQ.mem_nhds hz) (hV.mem_nhds hzV)) hpos)
  let K : Set (Point n) := closedBall z.1 r ×ˢ Icc (z.2-r) (z.2+r)
  have hKQ : K ⊆ Q := fun _ hp => (hK hp).1.1
  have hKV : K ⊆ V := fun _ hp => (hK hp).1.2
  let g : Point n → ℝ := fun q => u q-psi q
  have hg : ContinuousOn g K := (hu.1.mono hKQ).sub
    (fun q hq => (hpsiV q (hKV hq)).continuousAt.continuousWithinAt)
  have hslice : ∀ x∈closedBall z.1 r, g (x,z.2) = -‖x-z.1‖^4 := by
    intro x hx
    dsimp only [g,psi,perronQuartic,qnorm2]
    simp only [Prod.fst_sub,Prod.snd_sub,sub_self,zero_pow (by norm_num : 2≠0),add_zero]
    ring
  obtain ⟨J,p,hJ,hp,hmax⟩ := perturb_penalty_contact z hr hr g hg hslice
  have hpK : p ∈ K := ⟨ball_subset_closedBall hp.1,hp.2.1.le,hp.2.2.le⟩
  let c : ℝ := g p-J*(p.2-z.2)^2
  let phi : Point n → ℝ := fun q => psi q+(J*(q.2-z.2)^2+c)
  have hphi : ContDiffAt ℝ 2 phi p := (hpsiV p (hKV hpK)).add (by fun_prop)
  have ht : touchAbove phi u p := by
    refine ⟨?_,?_⟩
    · dsimp only [phi,c,g]
      ring
    · filter_upwards [hmax] with q hq
      change g q-J*(q.2-z.2)^2≤g p-J*(p.2-z.2)^2 at hq
      dsimp only [g] at hq
      dsimp only [phi,c,g]
      linarith
  have htime := (parabolic_touchAbove_jets hQ hu (hKQ hpK) hphi ht).1
  have hHphi : hessian phi p=hessian psi p :=
    perturb_hessian_add_time psi (fun t => J*(t-z.2)^2+c) p
  have hs := hsub p (hKQ hpK) phi hphi ht
  change timeD univ phi p-F (hessian phi p)≤0 at hs
  rw [←htime,hHphi] at hs
  have hgap := (hK hpK).2
  change 0<timeD Q u p-F (hessian psi p) at hgap
  linarith


theorem perturb_timeD_neg {n : ℕ} (Q : Set (Point n)) (u : Point n → ℝ) (p : Point n) :
    timeD Q (fun q => -u q) p= -timeD Q u p := derivWithin.fun_neg

theorem perturb_hessian_neg {n : ℕ} (u : Point n → ℝ) (p : Point n) :
    hessian (fun q => -u q) p= -hessian u p := by
  have hd : fderiv ℝ (fun x : Space n => -u (x,p.2))=
      fun x => -fderiv ℝ (fun y : Space n => u (y,p.2)) x :=
    funext (fun _ => fderiv_fun_neg)
  have hdd : spatialDD (fun q => -u q) p= -spatialDD u p := by
    unfold spatialDD
    rw [hd,fderiv_fun_neg]
  have hm : (fun i j => spatialDD (fun q => -u q) p (realVec i) (realVec j) : Mat n)=
      -(fun i j => spatialDD u p (realVec i) (realVec j) : Mat n) := by
    ext i j
    rw [hdd]
    rfl
  unfold hessian sym
  rw [hm]
  exact (selfAdjointPart ℝ).map_neg _

theorem perturb_c2_neg {n : ℕ} {Q : Set (Point n)} {u : Point n → ℝ}
    (hu : C2 Q u) : C2 Q (fun p => -u p) := by
  simpa only [zero_sub] using L16Aux.c2_sub (L16Aux.c2_zero Q) hu

theorem perturb_viscosity_super_neg {n : ℕ} {Q : Set (Point n)}
    {F : Sym n → ℝ} {u : Point n → ℝ}
    (hu : viscositySuper Q (fun H _ => F H) (fun _ => 0) u) :
    viscositySub Q (fun H _ => -F (-H)) (fun _ => 0) (fun p => -u p) := by
  intro p hp phi hphi ht
  have hn : touchBelow (fun q => -phi q) u p := by
    refine ⟨by linarith [ht.1],?_⟩
    filter_upwards [ht.2] with q hq
    linarith
  have hh := hu p hp (fun q => -phi q) hphi.neg hn
  change 0≤timeD univ (fun q => -phi q) p-F (hessian (fun q => -phi q) p) at hh
  rw [perturb_timeD_neg,perturb_hessian_neg] at hh
  change timeD univ phi p-(-F (-hessian phi p))≤0
  linarith

theorem perturb_actual_super_open {n : ℕ} {Q : Set (Point n)}
    (hQ : IsOpen Q) {F : Sym n → ℝ} (hF : Continuous F)
    {u : Point n → ℝ} (hu : C2 Q u)
    (hsuper : viscositySuper Q (fun H _ => F H) (fun _ => 0) u) :
    ∀ z∈Q, F (hessian u z)≤timeD Q u z := by
  have hFn : Continuous (fun H : Sym n => -F (-H)) := (hF.comp continuous_neg).neg
  have hh := perturb_actual_sub_open hQ hFn (perturb_c2_neg hu)
    (perturb_viscosity_super_neg hsuper)
  intro z hz
  have h := hh z hz
  rw [perturb_timeD_neg,perturb_hessian_neg,neg_neg] at h
  linarith

theorem perturb_actual_equation_open {n : ℕ} {Q : Set (Point n)}
    (hQ : IsOpen Q) {F : Sym n → ℝ} (hF : Continuous F)
    {u : Point n → ℝ} (hu : C2 Q u)
    (hs : viscositySolution Q (fun H _ => F H) (fun _ => 0) u) :
    ∀ p∈Q, timeD Q u p=F (hessian u p) := by
  intro p hp
  exact le_antisymm (perturb_actual_sub_open hQ hF hu hs.1 p hp)
    (perturb_actual_super_open hQ hF hu hs.2 p hp)


theorem perturb_c2_hessian_continuousOn {n : ℕ} {Q : Set (Point n)}
    {u : Point n → ℝ} (hu : C2 Q u) : ContinuousOn (hessian u) Q := by
  have hd : ContinuousOn (spatialDD u) Q := hu.2.2.1
  have hm : ContinuousOn (fun p : Point n =>
      (fun i j => spatialDD u p (realVec i) (realVec j) : Mat n)) Q := by
    fun_prop
  exact (selfAdjointPartL ℝ (Mat n)).continuous.comp_continuousOn hm

theorem perturb_actual_equation_top {n : ℕ} {R : ℝ} (hR : 0<R)
    {F : Sym n → ℝ} (hF : Continuous F) {u : Point n → ℝ}
    (hu : C2 (backward R) u)
    (hs : viscositySolution (perturbOpen (0 : Space n) R 0)
      (fun H _ => F H) (fun _ => 0) u) :
    ∀ p∈backward R, timeD (backward R) u p=F (hessian u p) := by
  let O : Set (Point n) := perturbOpen (0 : Space n) R 0
  have hO : IsOpen O := perturbOpen_isOpen _ _ _
  have hOB : O ⊆ backward R := by
    simpa only [perturbBack_zero] using perturbOpen_subset_back (0 : Space n) R 0
  have hC2 := c2_open_restrict hO hOB hu
  have heq := perturb_actual_equation_open hO hF hC2 hs
  let g : Point n → ℝ := fun p => timeD (backward R) u p-F (hessian u p)
  have hg : ContinuousOn g (backward R) :=
    hu.2.2.2.1.sub (hF.comp_continuousOn (perturb_c2_hessian_continuousOn hu))
  have hzero : ∀ p∈O, g p=0 := by
    intro p hp
    dsimp only [g]
    rw [←timeD_open_restrict hO hOB u hp,heq p hp,sub_self]
  intro p hp
  have hpcl : p∈closure O := by
    change p∈closure (ball (0 : Space n) R ×ˢ Ioo (0-R^2) 0)
    rw [closure_prod_eq,closure_Ioo (by nlinarith [sq_pos_of_pos hR] : 0-R^2≠0)]
    exact ⟨subset_closure hp.1,by simpa using ⟨hp.2.1.le,hp.2.2⟩⟩
  haveI : NeBot (𝓝[O] p) := mem_closure_iff_nhdsWithin_neBot.mp hpcl
  have ht : Tendsto g (𝓝[O] p) (𝓝 (g p)) := (hg p hp).mono hOB
  have he : g =ᶠ[𝓝[O] p] fun _ => 0 := by
    filter_upwards [self_mem_nhdsWithin] with q hq
    exact hzero q hq
  have h0 : Tendsto g (𝓝[O] p) (𝓝 0) := (tendsto_congr' he).mpr tendsto_const_nhds
  have hh := tendsto_nhds_unique ht h0
  exact sub_eq_zero.mp hh

end Yau.LeafProofs.L05Aux
