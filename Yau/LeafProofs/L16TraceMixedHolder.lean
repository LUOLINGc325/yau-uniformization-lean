import Yau.LeafProofs.L16TraceLayerMixed
import Yau.LeafProofs.L16TraceTangentialHolder

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 2000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates
local instance traceMixedHolder_normedAddCommGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance traceMixedHolder_normedSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- The genuine mixed integrand is absolutely integrable, including height zero. -/
theorem normalTraceMixed_integrable {n : ℕ} {α F H t : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ s x y, |B (x,s)-B (y,s)| ≤ H*‖x-y‖^α)
    (ht : 0 ≤ t) (a : ℝ) (ξ : Space n) :
    IntervalIntegrable (fun r : ℝ => (2*normalGaussianKernel r a) •
      fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ) volume 0 t := by
  rcases ht.eq_or_lt with rfl | ht
  · exact IntervalIntegrable.refl
  obtain ⟨C,hC,hMixed⟩ := traceMixedKernel_bound (n := n) hα.le
  let μ : Measure ℝ := volume.restrict (Ioo 0 t)
  have hm : AEStronglyMeasurable (fun r : ℝ => (2*normalGaussianKernel r a) •
      fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ) μ :=
    ((normalGaussianKernel_time_measurable a).const_mul 2).aestronglyMeasurable.smul
      ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
        (retardedHeatAverage_fderiv_time_integrable hB hF ht ξ)).aestronglyMeasurable
  have hPower : IntervalIntegrable (fun r : ℝ => r^(α/2-1)) volume 0 t :=
    intervalIntegral.intervalIntegrable_rpow' (by linarith)
  apply (intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mpr
  apply ((intervalIntegrable_iff_integrableOn_Ioo_of_le ht.le).mp
    (hPower.const_mul (C*H))).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
  exact hMixed B F H hB hF hH0 hH r hr.1 t a ξ

/-- The actual heat gradient is Lipschitz in location by its genuine Hessian. -/
theorem heatAverage_fderiv_spatial_increment_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ (g : Space n → ℝ) (F H : ℝ),
      Continuous g → (∀ y, |g y| ≤ F) → 0 ≤ H →
      (∀ x y, |g x-g y| ≤ H*‖x-y‖^α) → ∀ ξ η : Space n,
        ‖fderiv ℝ (heatAverage r g) ξ-fderiv ℝ (heatAverage r g) η‖ ≤
          C*H*‖ξ-η‖*r^(α/2-1) := by
  obtain ⟨C,hC,hHess⟩ := heatAverage_secondFDeriv_holder_bound (n := n) hα
  refine ⟨C,hC,?_⟩
  intro r hr g F H hg hF hH0 hH ξ η
  have hh := Convex.norm_image_sub_le_of_norm_fderiv_le
    (s := (univ : Set (Space n)))
    (fun x _ => (heatAverage_fderiv_hasFDerivAt_kernel_of_bounded hr hg hF x).differentiableAt)
    (fun x _ => hHess r hr g F H hg hF hH0 hH x)
    convex_univ (mem_univ η) (mem_univ ξ)
  convert hh using 1; ring

/-- Height increments of the real Gaussian normal derivative, including the face. -/
theorem normalGaussianKernel_normal_increment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      |2*normalGaussianKernel r a-2*normalGaussianKernel r b| ≤ C*|a-b|/r := by
  obtain ⟨C,hC,hP⟩ := normalPoissonKernel_uniform_age_bound
  refine ⟨C,hC,?_⟩
  intro r hr a b ha hb
  have hD (u : ℝ) : HasDerivAt (fun c => 2*normalGaussianKernel r c) (-normalPoissonKernel u r) u := by
    convert (normalGaussianKernel_hasDerivAt r u).const_mul 2 using 1
    dsimp only [normalPoissonKernel]; ring
  have hh := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u (_hu : u ∈ Ici (0 : ℝ)) => (hD u).differentiableAt)
    (fun u (hu : u ∈ Ici (0 : ℝ)) => by
      rw [(hD u).deriv,Real.norm_eq_abs,abs_neg,abs_of_nonneg (normalPoissonKernel_nonneg hu hr)]
      exact hP r hr u hu)
    (convex_Ici (0 : ℝ)) hb ha
  simp only [Real.norm_eq_abs] at hh
  convert hh using 1; ring

/-- The actual time derivative of the scalar Gaussian, obtained from its formula. -/
theorem normalGaussianKernel_time_hasDerivAt {r : ℝ} (hr : 0 < r) (a : ℝ) :
    HasDerivAt (fun u => normalGaussianKernel u a)
      (normalGaussianKernel r a*(a^2/(4*r^2)-1/(2*r))) r := by
  let c : ℝ := (Real.sqrt (4*Real.pi))⁻¹
  have hform (u : ℝ) (hu : 0 < u) : normalGaussianKernel u a =
      c*u^(-(1/2 : ℝ))*Real.exp (-(a^2/4)*u⁻¹) := by
    rw [normalGaussianKernel,Real.sqrt_mul (by positivity : 0 ≤ 4*Real.pi),mul_inv_rev,
      Real.sqrt_eq_rpow,← Real.rpow_neg hu.le]
    dsimp only [c]
    congr 1 <;> ring_nf
  have hp := (Real.hasDerivAt_rpow_const (p := -(1/2 : ℝ)) (Or.inl hr.ne')).const_mul c
  have he := (((hasDerivAt_id r).inv hr.ne').const_mul (-(a^2/4))).exp
  have hd := hp.mul he
  simp only [Pi.inv_apply,id_eq] at hd
  have hPow : r^(-(1/2 : ℝ)-1) = r^(-(1/2 : ℝ))/r := by
    rw [Real.rpow_sub hr,Real.rpow_one]
  have hEq : (fun u => normalGaussianKernel u a) =ᶠ[𝓝 r]
      (fun u => c*u^(-(1/2 : ℝ))*Real.exp (-(a^2/4)*u⁻¹)) := by
    filter_upwards [eventually_gt_nhds hr] with u hu
    exact hform u hu
  apply hEq.hasDerivAt_iff.mpr
  convert hd using 1
  rw [hform r hr,hPow]
  field_simp
  ring

/-- Uniform scalar Gaussian time derivative bound from an actual quadratic moment. -/
theorem normalGaussianKernel_time_deriv_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ a : ℝ, 0 ≤ a →
      |deriv (fun u => normalGaussianKernel u a) r| ≤ C*r^(-(3/2 : ℝ)) := by
  obtain ⟨C,hC,hG⟩ := gaussian_weight_bounded (s := 2) (b := 1/4) (by norm_num) (by norm_num)
  let c : ℝ := (Real.sqrt (4*Real.pi))⁻¹
  have hc : 0 < c := by dsimp [c]; positivity
  refine ⟨c*(C/4+1/2),by positivity,?_⟩
  intro r hr a ha
  let z : ℝ := a/Real.sqrt r
  have hs : Real.sqrt r ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hr)
  have hSc := normalGaussianKernel_sqrt_scaling hr z
  have hz : Real.sqrt r*z = a := by dsimp [z]; field_simp
  rw [hz] at hSc
  have hMoment : z^2*normalGaussianKernel 1 z ≤ c*C := by
    calc
      _ = c*(z^2*Real.exp (-(1/4 : ℝ)*z^2)) := by dsimp [normalGaussianKernel,c]; norm_num; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (by simpa only [Real.rpow_two] using hG z (by dsimp [z]; positivity)) hc.le
  have hQuadratic : a^2*normalGaussianKernel r a ≤ c*C*Real.sqrt r := by
    have he : a^2*normalGaussianKernel r a = Real.sqrt r*(z^2*normalGaussianKernel 1 z) := by
      rw [← hSc]
      dsimp [z]
      field_simp
    rw [he]
    convert mul_le_mul_of_nonneg_left hMoment (Real.sqrt_nonneg r) using 1; ring
  have hPow : r^(-(1/2 : ℝ))/r = r^(-(3/2 : ℝ)) := by
    simpa only [show -(1/2 : ℝ)-1 = -(3/2 : ℝ) by ring,Real.rpow_one] using
      (Real.rpow_sub hr (-(1/2 : ℝ)) 1).symm
  have hSqrt : Real.sqrt r = r*r^(-(1/2 : ℝ)) := by
    rw [Real.sqrt_eq_rpow]
    calc
      _ = r^((1 : ℝ)+(-(1/2 : ℝ))) := by congr 1; ring
      _ = _ := by rw [Real.rpow_add hr,Real.rpow_one]
  rw [(normalGaussianKernel_time_hasDerivAt hr a).deriv,abs_mul,
    abs_of_pos (normalGaussianKernel_pos hr a)]
  have hpoly : |a^2/(4*r^2)-1/(2*r)| ≤ a^2/(4*r^2)+1/(2*r) :=
    by
      convert abs_sub (a^2/(4*r^2)) (1/(2*r)) using 1
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
  calc
    _ ≤ normalGaussianKernel r a*(a^2/(4*r^2)+1/(2*r)) :=
      mul_le_mul_of_nonneg_left hpoly (normalGaussianKernel_pos hr a).le
    _ = (a^2*normalGaussianKernel r a)/(4*r^2)+normalGaussianKernel r a/(2*r) := by ring
    _ ≤ (c*C*Real.sqrt r)/(4*r^2)+(c*r^(-(1/2 : ℝ)))/(2*r) := add_le_add
      (div_le_div_of_nonneg_right hQuadratic (by positivity))
      (div_le_div_of_nonneg_right (normalGaussianKernel_le_rpow hr a) (by positivity))
    _ = c*(C/4+1/2)*(r^(-(1/2 : ℝ))/r) := by rw [hSqrt]; field_simp
    _ = _ := by rw [hPow]

/-- Gaussian age increments on the full nonnegative normal face. -/
theorem normalGaussianKernel_time_increment_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → ∀ δ : ℝ, 0 ≤ δ →
      ∀ a : ℝ, 0 ≤ a → |2*normalGaussianKernel (r+δ) a-2*normalGaussianKernel r a| ≤
        C*δ*r^(-(3/2 : ℝ)) := by
  obtain ⟨C,hC,hD⟩ := normalGaussianKernel_time_deriv_bound
  refine ⟨2*C,by positivity,?_⟩
  intro r hr δ hδ a ha
  have hle : r ≤ r+δ := le_add_of_nonneg_right hδ
  have hMean := Convex.norm_image_sub_le_of_norm_deriv_le
    (fun u (hu : u ∈ Icc r (r+δ)) =>
      ((normalGaussianKernel_time_hasDerivAt (hr.trans_le hu.1) a).const_mul 2).differentiableAt)
    (fun u (hu : u ∈ Icc r (r+δ)) => by
      rw [((normalGaussianKernel_time_hasDerivAt (hr.trans_le hu.1) a).const_mul 2).deriv,
        Real.norm_eq_abs,abs_mul,abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
      have hh := hD u (hr.trans_le hu.1) a ha
      rw [(normalGaussianKernel_time_hasDerivAt (hr.trans_le hu.1) a).deriv] at hh
      exact mul_le_mul_of_nonneg_left (hh.trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos hr hu.1 (by norm_num : -(3/2 : ℝ) ≤ 0)) hC.le)) (by norm_num : (0:ℝ) ≤ 2))
    (convex_Icc r (r+δ)) (left_mem_Icc.mpr hle) (right_mem_Icc.mpr hle)
  simp only [Real.norm_eq_abs,add_sub_cancel_left,abs_of_nonneg hδ] at hMean
  convert hMean using 1; ring


/-- The actual age derivative of the first spatial Gaussian derivative. -/
theorem gaussianKernel_fderiv_time_hasDerivAt {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x : Space n) :
    HasDerivAt (fun r : ℝ => fderiv ℝ (gaussianKernel r) x)
      ((gaussianKernel t x*(((n:ℝ)+1)/(2*t^2)-‖x‖^2/(8*t^3))) • innerSL ℝ x) t := by
  have hp := (gaussianKernel_hasDerivAt ht x).neg.div
    ((hasDerivAt_id t).const_mul 2) (by positivity : 2*t ≠ 0)
  have hh := hp.smul_const (innerSL ℝ x)
  have hEq : (fun r : ℝ => fderiv ℝ (gaussianKernel r) x) =ᶠ[𝓝 t]
      (fun r => (-gaussianKernel r x/(2*r)) • innerSL ℝ x) := by
    filter_upwards [eventually_gt_nhds ht] with r hr
    exact (gaussianKernel_hasFDerivAt hr x).fderiv
  apply hEq.hasDerivAt_iff.mpr
  convert hh using 1
  congr 1
  dsimp only [id_eq,Pi.neg_apply,Pi.div_apply,Pi.mul_apply]
  field_simp
  ring_nf

theorem gaussianKernel_fderiv_time_joint_smooth {n : ℕ} {t : ℝ}
    (ht : 0 < t) (x : Space n) :
    ContDiffAt ℝ ∞ (fun p : ℝ × Space n =>
      deriv (fun r : ℝ => fderiv ℝ (gaussianKernel r) p.2) p.1) (t,x) := by
  have hF : ContDiffAt ℝ ∞ (fun q : (ℝ × Space n) × ℝ =>
      fderiv ℝ (gaussianKernel q.2) q.1.2) ((t,x),t) :=
    ContDiffAt.comp (𝕜 := ℝ) (n := ∞)
      (g := fun p : ℝ × Space n => fderiv ℝ (gaussianKernel p.1) p.2)
      (f := fun q : (ℝ × Space n) × ℝ => (q.2,q.1.2))
      ((t,x),t) (gaussianKernel_fderiv_joint_smooth ht x) (by fun_prop)
  have hh : ContDiffAt ℝ ∞ (fun p : ℝ × Space n =>
      fderiv ℝ (fun r : ℝ => fderiv ℝ (gaussianKernel r) p.2) p.1) (t,x) :=
    ContDiffAt.fderiv (f := fun p : ℝ × Space n => fun r : ℝ =>
      fderiv ℝ (gaussianKernel r) p.2) (g := Prod.fst) hF contDiffAt_fst (by simp)
  simpa only [fderiv_apply_one_eq_deriv] using hh.clm_apply (contDiffAt_const (c := (1 : ℝ)))

/-- The Gaussian polynomial formula gives the genuine weighted time moment. -/
theorem gaussianKernel_fderiv_time_weight_bound {n : ℕ} {α : ℝ} (hα : 0 ≤ α) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t →
      Integrable (fun x : Space n =>
        ‖deriv (fun r : ℝ => fderiv ℝ (gaussianKernel r) x) t‖*‖x‖^α) ∧
      (∫ x : Space n,
        ‖deriv (fun r : ℝ => fderiv ℝ (gaussianKernel r) x) t‖*‖x‖^α) ≤ C*t^(α/2-3/2) := by
  obtain ⟨C3,hC3,hM3⟩ := gaussianKernel_weight_integral_bound (n := n) (s := α+3) (by linarith)
  obtain ⟨C1,hC1,hM1⟩ := gaussianKernel_weight_integral_bound (n := n) (s := α+1) (by linarith)
  let C : ℝ := C3/8+((n:ℝ)+1)*C1/2
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro t ht
  let g3 : Space n → ℝ := fun x => (1/(8*t^3))*(‖x‖^(α+3)*gaussianKernel t x)
  let g1 : Space n → ℝ := fun x => (((n:ℝ)+1)/(2*t^2))*(‖x‖^(α+1)*gaussianKernel t x)
  have hi3 : Integrable g3 := (hM3 t ht).1.const_mul _
  have hi1 : Integrable g1 := (hM1 t ht).1.const_mul _
  have hp3 (x : Space n) : ‖x‖^(α+3) = ‖x‖^α*‖x‖^3 := by
    simp only [Real.rpow_add_of_nonneg (norm_nonneg x) hα (show (0:ℝ) ≤ 3 by norm_num),Real.rpow_ofNat]
  have hp1 (x : Space n) : ‖x‖^(α+1) = ‖x‖^α*‖x‖ := by
    rw [Real.rpow_add_of_nonneg (norm_nonneg x) hα (by norm_num),Real.rpow_one]
  have hpoint (x : Space n) :
      ‖deriv (fun r : ℝ => fderiv ℝ (gaussianKernel r) x) t‖*‖x‖^α ≤ g3 x+g1 x := by
    have hpoly : |((n:ℝ)+1)/(2*t^2)-‖x‖^2/(8*t^3)| ≤
        ((n:ℝ)+1)/(2*t^2)+‖x‖^2/(8*t^3) := by
      convert abs_sub (((n:ℝ)+1)/(2*t^2)) (‖x‖^2/(8*t^3)) using 1
      rw [abs_of_nonneg (by positivity),abs_of_nonneg (by positivity)]
    rw [(gaussianKernel_fderiv_time_hasDerivAt ht x).deriv,norm_smul,Real.norm_eq_abs,
      abs_mul,abs_of_pos (gaussianKernel_pos ht x),innerSL_apply_norm]
    have hh := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpoly (gaussianKernel_pos ht x).le)
        (norm_nonneg x)) (Real.rpow_nonneg (norm_nonneg x) α)
    convert hh using 1
    dsimp [g3,g1]
    rw [hp3,hp1]
    ring
  have hc : Continuous (fun x : Space n =>
      ‖deriv (fun r : ℝ => fderiv ℝ (gaussianKernel r) x) t‖*‖x‖^α) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (((gaussianKernel_fderiv_time_joint_smooth ht x).continuousAt.comp
      (continuousAt_const.prodMk continuousAt_id)).norm).mul
        (((Real.continuous_rpow_const hα).comp continuous_norm).continuousAt)
  have hi : Integrable (fun x : Space n =>
      ‖deriv (fun r : ℝ => fderiv ℝ (gaussianKernel r) x) t‖*‖x‖^α) := by
    apply (hi3.add hi1).mono' hc.aestronglyMeasurable
    filter_upwards [] with x
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg x) _))]
    exact hpoint x
  refine ⟨hi,?_⟩
  have ht3 : t^((α+3)/2) = t^(α/2-3/2)*t^3 := by
    simp only [show (α+3)/2 = (α/2-3/2)+3 by ring,Real.rpow_add ht,Real.rpow_ofNat]
  have ht1 : t^((α+1)/2) = t^(α/2-3/2)*t^2 := by
    rw [show (α+1)/2 = (α/2-3/2)+2 by ring,Real.rpow_add ht,Real.rpow_two]
  calc
    _ ≤ ∫ x : Space n, g3 x+g1 x := integral_mono_ae hi (hi3.add hi1) (ae_of_all _ hpoint)
    _ = (1/(8*t^3))*(∫ x : Space n, ‖x‖^(α+3)*gaussianKernel t x)+
        (((n:ℝ)+1)/(2*t^2))*(∫ x : Space n, ‖x‖^(α+1)*gaussianKernel t x) := by
      rw [integral_add hi3 hi1]; simp only [g3,g1,integral_const_mul]
    _ ≤ (1/(8*t^3))*(C3*t^((α+3)/2))+
        (((n:ℝ)+1)/(2*t^2))*(C1*t^((α+1)/2)) := add_le_add
      (mul_le_mul_of_nonneg_left (hM3 t ht).2 (by positivity))
      (mul_le_mul_of_nonneg_left (hM1 t ht).2 (by positivity))
    _ = _ := by rw [ht3,ht1]; dsimp [C]; field_simp


theorem gaussianKernel_fderiv_temporal_increment_le {n : ℕ} {t δ : ℝ}
    (ht : 0 < t) (hδ : 0 ≤ δ) (y : Space n) :
    ‖fderiv ℝ (gaussianKernel (t+δ)) y -
      fderiv ℝ (gaussianKernel t) y‖ ≤
      ∫ r in t..t+δ,
        ‖deriv (fun s : ℝ => fderiv ℝ (gaussianKernel s) y) r‖ := by
  have hle : t ≤ t+δ := le_add_of_nonneg_right hδ
  have hHc : ContinuousOn (fun r : ℝ => fderiv ℝ (gaussianKernel r) y)
      (Set.Icc t (t+δ)) := by
    intro r hr
    have hh : ContinuousAt (fun s : ℝ => fderiv ℝ (gaussianKernel s) y) r :=
      ContinuousAt.comp (f := fun s : ℝ => (s,y))
        (g := fun p : ℝ × Space n => fderiv ℝ (gaussianKernel p.1) p.2)
        (gaussianKernel_fderiv_joint_smooth (ht.trans_le hr.1) y).continuousAt (by fun_prop)
    exact hh.continuousWithinAt
  have hDc : ContinuousOn (fun r : ℝ =>
      ‖deriv (fun s : ℝ => fderiv ℝ (gaussianKernel s) y) r‖)
      (Set.Icc t (t+δ)) := by
    intro r hr
    have hh : ContinuousAt (fun r : ℝ =>
        deriv (fun s : ℝ => fderiv ℝ (gaussianKernel s) y) r) r :=
      ContinuousAt.comp (f := fun s : ℝ => (s,y))
        (g := fun p : ℝ × Space n =>
          deriv (fun s : ℝ => fderiv ℝ (gaussianKernel s) p.2) p.1)
        (gaussianKernel_fderiv_time_joint_smooth (ht.trans_le hr.1) y).continuousAt (by fun_prop)
    exact hh.norm.continuousWithinAt
  exact norm_sub_le_integral_of_norm_deriv_le_of_le hle hHc
    (fun r hr => (gaussianKernel_fderiv_time_hasDerivAt (ht.trans hr.1) y).differentiableAt.differentiableWithinAt)
    (ae_of_all _ fun r _ => le_rfl) (hDc.intervalIntegrable_of_Icc hle)

theorem gaussianKernel_fderiv_time_increment_weight_bound {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ δ : ℝ, 0 ≤ δ →
      Integrable (fun y : Space n =>
        ‖fderiv ℝ (gaussianKernel (t+δ)) y -
          fderiv ℝ (gaussianKernel t) y‖ * ‖y‖^α) ∧
      (∫ y : Space n,
        ‖fderiv ℝ (gaussianKernel (t+δ)) y -
          fderiv ℝ (gaussianKernel t) y‖ * ‖y‖^α) ≤ C*δ*t^(α/2-3/2) := by
  obtain ⟨C,hC,hbound⟩ := gaussianKernel_fderiv_time_weight_bound (n := n) hα
  refine ⟨C,hC,?_⟩
  intro t ht δ hδ
  have htδ : 0 < t+δ := add_pos_of_pos_of_nonneg ht hδ
  have hle : t ≤ t+δ := le_add_of_nonneg_right hδ
  let μ : Measure ℝ := volume.restrict (Set.Ioc t (t+δ))
  let : IsFiniteMeasure μ := ⟨by simp [μ,Real.volume_Ioc]⟩
  let F : ℝ → Space n → ℝ := fun r y =>
    ‖deriv (fun s : ℝ => fderiv ℝ (gaussianKernel s) y) r‖*‖y‖^α
  have hFpos (r : ℝ) (y : Space n) : 0 ≤ F r y :=
    mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _)
  have hFI (r : ℝ) (hr : r ∈ Set.Ioc t (t+δ)) : Integrable (F r) :=
    (hbound r (ht.trans hr.1)).1
  have hFB (r : ℝ) (hr : r ∈ Set.Ioc t (t+δ)) :
      (∫ y : Space n, F r y) ≤ C*t^(α/2-3/2) := by
    exact ((hbound r (ht.trans hr.1)).2).trans
      (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow_of_nonpos ht hr.1.le (by linarith)) hC.le)
  have hFc : ContinuousOn (Function.uncurry F) (Set.Ioc t (t+δ) ×ˢ Set.univ) := by
    intro p hp
    exact (((gaussianKernel_fderiv_time_joint_smooth (ht.trans hp.1.1) p.2).continuousAt.norm).mul
      (((Real.continuous_rpow_const hα).comp continuous_norm).continuousAt.comp continuousAt_snd)).continuousWithinAt
  have hProd : μ.prod (volume : Measure (Space n)) =
      ((volume : Measure ℝ).prod (volume : Measure (Space n))).restrict
        (Set.Ioc t (t+δ) ×ˢ (Set.univ : Set (Space n))) := by
    simpa only [μ,Measure.restrict_univ] using
      (Measure.prod_restrict (μ := (volume : Measure ℝ))
        (ν := (volume : Measure (Space n))) (Set.Ioc t (t+δ)) Set.univ)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (μ.prod volume) := by
    rw [hProd]
    exact hFc.aestronglyMeasurable (measurableSet_Ioc.prod MeasurableSet.univ)
  have hFnI : Integrable (fun r : ℝ => ∫ y : Space n, ‖F r y‖) μ := by
    apply (integrable_const (C*t^(α/2-3/2))).mono' hFm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    have heq : (fun y : Space n => ‖F r y‖) = F r := by
      funext y
      exact Real.norm_of_nonneg (hFpos r y)
    change ‖∫ y : Space n, ‖F r y‖‖ ≤ C*t^(α/2-3/2)
    rw [heq,Real.norm_of_nonneg (integral_nonneg (hFpos r))]
    exact hFB r hr
  have hprod : Integrable (Function.uncurry F) (μ.prod volume) := by
    apply (integrable_prod_iff hFm).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
    exact hFI r hr
  have hQi := hprod.integral_prod_right
  have hpoint (y : Space n) :
      ‖fderiv ℝ (gaussianKernel (t+δ)) y -
        fderiv ℝ (gaussianKernel t) y‖*‖y‖^α ≤ ∫ r, F r y ∂μ := by
    have hb := mul_le_mul_of_nonneg_right
      (gaussianKernel_fderiv_temporal_increment_le ht hδ y)
      (Real.rpow_nonneg (norm_nonneg y) α)
    rw [intervalIntegral.integral_of_le hle] at hb
    simpa only [μ,F,integral_mul_const] using hb
  have hHc (r : ℝ) : Continuous (fun y : Space n => fderiv ℝ (gaussianKernel r) y) :=
    (gaussianKernel_spatial_smooth r).continuous_fderiv (by simp)
  have hc : Continuous (fun y : Space n =>
      ‖fderiv ℝ (gaussianKernel (t+δ)) y -
        fderiv ℝ (gaussianKernel t) y‖*‖y‖^α) :=
    ((hHc (t+δ)).sub (hHc t)).norm.mul ((Real.continuous_rpow_const hα).comp continuous_norm)
  have hi : Integrable (fun y : Space n =>
      ‖fderiv ℝ (gaussianKernel (t+δ)) y -
        fderiv ℝ (gaussianKernel t) y‖*‖y‖^α) := by
    apply hQi.mono' hc.aestronglyMeasurable
    filter_upwards [] with y
    rw [Real.norm_of_nonneg (mul_nonneg (norm_nonneg _) (Real.rpow_nonneg (norm_nonneg _) _))]
    exact hpoint y
  refine ⟨hi,?_⟩
  calc
    _ ≤ ∫ y : Space n, ∫ r, F r y ∂μ := integral_mono_ae hi hQi (ae_of_all _ hpoint)
    _ = ∫ r, (∫ y : Space n, F r y) ∂μ := (integral_integral_swap hprod).symm
    _ ≤ ∫ _r, C*t^(α/2-3/2) ∂μ := by
      apply integral_mono_ae hprod.integral_prod_left (integrable_const _)
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
      exact hFB r hr
    _ = C*δ*t^(α/2-3/2) := by
      simp only [integral_const]
      simp [μ,Measure.real,Real.volume_Ioc,ENNReal.toReal_ofReal hδ]; ring


theorem heatAverage_fderiv_time_increment_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ t : ℝ, 0 < t → ∀ δ : ℝ, 0 ≤ δ →
      ∀ (g : Space n → ℝ) (M H : ℝ), Continuous g → (∀ y, |g y| ≤ M) → 0 ≤ H →
      (∀ x y, |g x-g y| ≤ H*‖x-y‖^α) → ∀ x : Space n,
        ‖fderiv ℝ (heatAverage (t+δ) g) x -
          fderiv ℝ (heatAverage t g) x‖ ≤ C*H*δ*t^(α/2-3/2) := by
  obtain ⟨C,hC,hbound⟩ := gaussianKernel_fderiv_time_increment_weight_bound (n := n) hα hα1
  refine ⟨C,hC,?_⟩
  intro t ht δ hδ g M H hg hM hH0 hH x
  have htδ : 0 < t+δ := add_pos_of_pos_of_nonneg ht hδ
  let D : ℝ → Space n → Space n →L[ℝ] ℝ :=
    fun r => fderiv ℝ (gaussianKernel r)
  let K : Space n → Space n →L[ℝ] ℝ := fun y => D (t+δ) y-D t y
  have hDc (r : ℝ) : Continuous (D r) :=
    (gaussianKernel_spatial_smooth (n := n) r).continuous_fderiv (by simp)
  have hDi (r : ℝ) (hr : 0 < r) : Integrable (D r) := gaussianKernel_fderiv_integrable hr
  have hKc : Continuous K := (hDc (t+δ)).sub (hDc t)
  have hKi : Integrable K := (hDi (t+δ) htδ).sub (hDi t ht)
  have hK0 : (∫ y : Space n, K y) = 0 := by
    dsimp [K,D]
    rw [integral_sub (hDi (t+δ) htδ) (hDi t ht),
      gaussianKernel_fderiv_integral_zero htδ,gaussianKernel_fderiv_integral_zero ht,sub_self]
  have hi (r : ℝ) (hr : 0 < r) : Integrable (fun y : Space n => g y • D r (x-y)) := by
    convert ((hDi r hr).comp_sub_left x).bdd_smul M hg.aestronglyMeasurable
      (ae_of_all _ fun y => by simpa only [Real.norm_eq_abs] using hM y) using 1
  have heq : fderiv ℝ (heatAverage (t+δ) g) x -
        fderiv ℝ (heatAverage t g) x =
      ∫ y : Space n, (g (x-y)-g x) • K y := by
    rw [(heatAverage_hasFDerivAt_kernel_of_bounded htδ hg hM x).fderiv,
      (heatAverage_hasFDerivAt_kernel_of_bounded ht hg hM x).fderiv]
    calc
      _ = ∫ y : Space n, g y • D (t+δ) (x-y)-g y • D t (x-y) :=
        (integral_sub (hi (t+δ) htδ) (hi t ht)).symm
      _ = ∫ y : Space n, g (x-y) • D (t+δ) (x-(x-y))-g (x-y) • D t (x-(x-y)) :=
        (integral_sub_left_eq_self
          (fun y : Space n => g y • D (t+δ) (x-y)-g y • D t (x-y)) volume x).symm
      _ = ∫ y : Space n, g (x-y) • K y := by
        congr 1
        funext y
        rw [sub_sub_cancel,← smul_sub]
      _ = _ := integral_smul_sub_const_of_zero_integral hKc hKi.norm hK0
        (hg.comp (continuous_const.sub continuous_id)) (fun y => hM (x-y)) (g x)
  rw [heq]
  calc
    _ ≤ ∫ y : Space n, H*(‖K y‖*‖y‖^α) := by
      apply norm_integral_le_of_norm_le ((hbound t ht δ hδ).1.const_mul H)
      filter_upwards [] with y
      have hy := hH (x-y) x
      have he : (x-y)-x = -y := by abel
      rw [he,norm_neg] at hy
      calc
        _ ≤ ‖g (x-y)-g x‖*‖K y‖ := ContinuousLinearMap.opNorm_smul_le _ _
        _ = |g (x-y)-g x| * ‖K y‖ := by rw [Real.norm_eq_abs]
        _ ≤ (H*‖y‖^α)*‖K y‖ := mul_le_mul_of_nonneg_right hy (K y).opNorm_nonneg
        _ = _ := by ring
    _ = H*(∫ y : Space n, ‖K y‖*‖y‖^α) := integral_const_mul _ _
    _ ≤ H*(C*δ*t^(α/2-3/2)) := mul_le_mul_of_nonneg_left (hbound t ht δ hδ).2 hH0
    _ = C*H*δ*t^(α/2-3/2) := by ring




/-- Location Holder continuity of the actual mixed jet. -/
theorem normalTraceMixed_spatial_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ σ x y, |B (x,σ)-B (y,σ)| ≤ H*‖x-y‖^α) →
      ∀ t a : ℝ, 0 ≤ t → ∀ ξ η : Space n,
        ‖normalTraceMixed B t a ξ-normalTraceMixed B t a η‖ ≤ C*H*‖ξ-η‖^α := by
  obtain ⟨C0,hC0,hMixed⟩ := traceMixedKernel_bound (n := n) hα.le
  obtain ⟨C1,hC1,hInc⟩ := heatAverage_fderiv_spatial_increment_holder_bound (n := n) hα.le
  let Cg : ℝ := 2*(Real.sqrt (4*Real.pi))⁻¹
  have hCg : 0 < Cg := by dsimp [Cg]; positivity
  let C : ℝ := 4*C0/α+2*(Cg*C1)/(1-α)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro B F H hB hF hH0 hH t a ht ξ η
  rcases ht.eq_or_lt with rfl | ht
  · rw [normalTraceMixed_initial,normalTraceMixed_initial,sub_self,norm_zero]
    positivity
  by_cases hξη : ξ = η
  · subst η
    simp only [sub_self,norm_zero,Real.zero_rpow hα.ne',mul_zero,le_refl]
  have hd : 0 < ‖ξ-η‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hξη)
  let K : ℝ → Space n →L[ℝ] ℝ := fun r => (2*normalGaussianKernel r a) •
    (fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ-fderiv ℝ (heatAverage r (fun y => B (y,t-r))) η)
  have hIξ := normalTraceMixed_integrable hα hB hF hH0 hH ht.le a ξ
  have hIη := normalTraceMixed_integrable hα hB hF hH0 hH ht.le a η
  have hKi : IntervalIntegrable K volume 0 t := by simpa only [K,smul_sub] using hIξ.sub hIη
  have heq : normalTraceMixed B t a ξ-normalTraceMixed B t a η = ∫ r in (0 : ℝ)..t, K r := by
    rw [normalTraceMixed,normalTraceMixed,← intervalIntegral.integral_sub hIξ hIη]
    simp only [K,smul_sub]
  have hnear (r : ℝ) (hr : r ∈ Ioc 0 t) : ‖K r‖ ≤ (2*C0*H)*r^(α/2-1) := by
    dsimp only [K]; rw [smul_sub]
    exact (norm_sub_le _ _).trans (by
      convert add_le_add (hMixed B F H hB hF hH0 hH r hr.1 t a ξ)
        (hMixed B F H hB hF hH0 hH r hr.1 t a η) using 1; ring)
  have hfar (r : ℝ) (hr : r ∈ Ioc (‖ξ-η‖^2) t) :
      ‖K r‖ ≤ ((Cg*C1)*H)*‖ξ-η‖*r^(α/2-3/2) := by
    have hr0 : 0 < r := (sq_pos_of_pos hd).trans hr.1
    have hg0 : 0 ≤ 2*normalGaussianKernel r a := mul_nonneg (by norm_num) (normalGaussianKernel_pos hr0 a).le
    have hg : 2*normalGaussianKernel r a ≤ Cg*r^(-(1/2 : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left (normalGaussianKernel_le_rpow hr0 a) (by norm_num : (0:ℝ) ≤ 2)
      simpa only [Cg,mul_assoc] using hh
    have hPow : r^(-(1/2 : ℝ))*r^(α/2-1) = r^(α/2-3/2) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    dsimp only [K]; rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hg0]
    calc
      _ ≤ (Cg*r^(-(1/2 : ℝ)))*(C1*H*‖ξ-η‖*r^(α/2-1)) := mul_le_mul hg
        (hInc r hr0 (fun y => B (y,t-r)) F H (hB.comp (continuous_id.prodMk continuous_const))
          (fun y => hF (y,t-r)) hH0 (hH (t-r)) ξ η) (norm_nonneg _) (by positivity)
      _ = ((Cg*C1)*H)*‖ξ-η‖*(r^(-(1/2 : ℝ))*r^(α/2-1)) := by ring
      _ = _ := by rw [hPow]
  rw [heq]
  have hh := schauder_spatial_near_far_integral_bound hα hα1
    (by positivity : 0 ≤ 2*C0*H) (by positivity : 0 ≤ (Cg*C1)*H) hd ht hKi hnear hfar
  convert hh using 1; dsimp [C]; ring

/-- Normal-height Holder continuity of the mixed jet; its face value is retained. -/
theorem normalTraceMixed_normal_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ σ x y, |B (x,σ)-B (y,σ)| ≤ H*‖x-y‖^α) →
      ∀ t a b : ℝ, 0 ≤ t → 0 ≤ a → 0 ≤ b → ∀ ξ : Space n,
        ‖normalTraceMixed B t a ξ-normalTraceMixed B t b ξ‖ ≤ C*H*|a-b|^α := by
  obtain ⟨C0,hC0,hMixed⟩ := traceMixedKernel_bound (n := n) hα.le
  obtain ⟨C1,hC1,hGrad⟩ := heatAverage_fderiv_holder_bound (n := n) hα.le
  obtain ⟨Cp,hCp,hInc⟩ := normalGaussianKernel_normal_increment_bound
  let C : ℝ := 4*C0/α+2*(Cp*C1)/(1-α)
  refine ⟨C,by dsimp [C]; positivity,?_⟩
  intro B F H hB hF hH0 hH t a b ht ha hb ξ
  rcases ht.eq_or_lt with rfl | ht
  · rw [normalTraceMixed_initial,normalTraceMixed_initial,sub_self,norm_zero]
    positivity
  by_cases hab : a = b
  · subst b
    simp only [sub_self,norm_zero,abs_zero,Real.zero_rpow hα.ne',mul_zero,le_refl]
  have hd : 0 < |a-b| := abs_pos.mpr (sub_ne_zero.mpr hab)
  let K : ℝ → Space n →L[ℝ] ℝ := fun r =>
    (2*normalGaussianKernel r a-2*normalGaussianKernel r b) • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ
  have hIa := normalTraceMixed_integrable hα hB hF hH0 hH ht.le a ξ
  have hIb := normalTraceMixed_integrable hα hB hF hH0 hH ht.le b ξ
  have hKi : IntervalIntegrable K volume 0 t := by simpa only [K,sub_smul] using hIa.sub hIb
  have heq : normalTraceMixed B t a ξ-normalTraceMixed B t b ξ = ∫ r in (0 : ℝ)..t, K r := by
    rw [normalTraceMixed,normalTraceMixed,← intervalIntegral.integral_sub hIa hIb]
    simp only [K,sub_smul]
  have hnear (r : ℝ) (hr : r ∈ Ioc 0 t) : ‖K r‖ ≤ (2*C0*H)*r^(α/2-1) := by
    dsimp only [K]; rw [sub_smul]
    exact (norm_sub_le _ _).trans (by
      convert add_le_add (hMixed B F H hB hF hH0 hH r hr.1 t a ξ)
        (hMixed B F H hB hF hH0 hH r hr.1 t b ξ) using 1; ring)
  have hfar (r : ℝ) (hr : r ∈ Ioc (|a-b|^2) t) :
      ‖K r‖ ≤ ((Cp*C1)*H)*|a-b| *r^(α/2-3/2) := by
    have hr0 : 0 < r := (sq_pos_of_pos hd).trans hr.1
    have hPow : r^(α/2-1/2)/r = r^(α/2-3/2) := by
      simpa only [Real.rpow_one,show (α/2-1/2)-1 = α/2-3/2 by ring] using
        (Real.rpow_sub hr0 (α/2-1/2) 1).symm
    dsimp only [K]; rw [norm_smul,Real.norm_eq_abs]
    calc
      _ ≤ (Cp*|a-b|/r)*(C1*H*r^(α/2-1/2)) := mul_le_mul (hInc r hr0 a b ha hb)
        (hGrad r hr0 (fun y => B (y,t-r)) F H (hB.comp (continuous_id.prodMk continuous_const))
          (fun y => hF (y,t-r)) hH0 (hH (t-r)) ξ) (norm_nonneg _) (by positivity)
      _ = ((Cp*C1)*H)*|a-b| *(r^(α/2-1/2)/r) := by ring
      _ = _ := by rw [hPow]
  rw [heq]
  have hh := schauder_spatial_near_far_integral_bound hα hα1
    (by positivity : 0 ≤ 2*C0*H) (by positivity : 0 ≤ (Cp*C1)*H) hd ht hKi hnear hfar
  convert hh using 1; dsimp [C]; ring


/-- Source-time coordinates preserve genuine mixed-kernel integrability. -/
theorem normalTraceMixed_source_integrable {n : ℕ} {α F H t : ℝ}
    (hα : 0 < α) {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F)
    (hH0 : 0 ≤ H) (hH : ∀ σ x y, |B (x,σ)-B (y,σ)| ≤ H*‖x-y‖^α)
    (ht : 0 ≤ t) (a : ℝ) (ξ : Space n) :
    IntervalIntegrable (fun σ : ℝ => (2*normalGaussianKernel (t-σ) a) •
      fderiv ℝ (heatAverage (t-σ) (fun y => B (y,σ))) ξ) volume 0 t := by
  simpa only [sub_zero,sub_self,sub_sub_cancel] using
    ((normalTraceMixed_integrable hα hB hF hH0 hH ht a ξ).comp_sub_left t).symm

/-- Time Holder continuity of the actual mixed integral, without time differentiation of B. -/
theorem normalTraceMixed_temporal_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F H : ℝ),
      Continuous B → (∀ p, |B p| ≤ F) → 0 ≤ H →
      (∀ σ x y, |B (x,σ)-B (y,σ)| ≤ H*‖x-y‖^α) →
      ∀ t δ a : ℝ, 0 ≤ t → 0 ≤ δ → 0 ≤ a → ∀ ξ : Space n,
        ‖normalTraceMixed B (t+δ) a ξ-normalTraceMixed B t a ξ‖ ≤
          C*H*δ^(α/2) := by
  obtain ⟨C0,hC0,hInit⟩ := normalTraceMixed_bound (n := n) hα
  obtain ⟨C2,hC2,hMixed⟩ := traceMixedKernel_bound (n := n) hα.le
  obtain ⟨Cg,hCg,hGrad⟩ := heatAverage_fderiv_holder_bound (n := n) hα.le
  obtain ⟨C3,hC3,hInc⟩ := heatAverage_fderiv_time_increment_holder_bound (n := n) hα.le hα1.le
  obtain ⟨Cp,hCp,hProfile⟩ := normalGaussianKernel_time_increment_bound
  let Ck : ℝ := 2*(Real.sqrt (4*Real.pi))⁻¹
  have hCk : 0 < Ck := by dsimp [Ck]; positivity
  let C4 : ℝ := Ck*C3+Cp*Cg
  have hC4 : 0 < C4 := by dsimp [C4]; positivity
  have hTwo : 0 < 2-α := by linarith
  let C : ℝ := C0+6*C2/α+2*C4/(2-α)
  have hC : 0 < C := by dsimp [C]; positivity
  have hC0C : C0 ≤ C := by
    have h1 : 0 ≤ 6*C2/α := by positivity
    have h2 : 0 ≤ 2*C4/(2-α) := by positivity
    dsimp [C]; linarith
  have hRestC : 6*C2/α+2*C4/(2-α) ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro B F H hB hF hH0 hH t δ a ht hδ ha ξ
  rcases hδ.eq_or_lt with rfl | hδ
  · simp only [add_zero,sub_self,norm_zero,Real.zero_rpow (by positivity : α/2 ≠ 0),mul_zero,le_refl]
  rcases ht.eq_or_lt with rfl | ht
  · rw [zero_add,normalTraceMixed_initial,sub_zero]
    exact (hInit B F H hB hF hH0 hH δ hδ.le a ξ).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hC0C hH0)
        (Real.rpow_nonneg hδ.le _))
  have htδ : 0 < t+δ := by positivity
  have hle : t ≤ t+δ := le_add_of_nonneg_right hδ.le
  have hfc (σ : ℝ) : Continuous (fun y : Space n => B (y,σ)) :=
    hB.comp (continuous_id.prodMk continuous_const)
  have hFs (σ : ℝ) (y : Space n) : |B (y,σ)| ≤ F := hF (y,σ)
  let N : ℝ → Space n →L[ℝ] ℝ := fun σ =>
    (2*normalGaussianKernel (t+δ-σ) a) •
      fderiv ℝ (heatAverage (t+δ-σ) (fun y => B (y,σ))) ξ
  let O : ℝ → Space n →L[ℝ] ℝ := fun σ =>
    (2*normalGaussianKernel (t-σ) a) •
      fderiv ℝ (heatAverage (t-σ) (fun y => B (y,σ))) ξ
  let A : ℝ → Space n →L[ℝ] ℝ := fun σ => N σ-O σ
  let K : ℝ → Space n →L[ℝ] ℝ := fun r =>
    (2*normalGaussianKernel (r+δ) a) •
      fderiv ℝ (heatAverage (r+δ) (fun y => B (y,t-r))) ξ -
    (2*normalGaussianKernel r a) •
      fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ
  have hNall : IntervalIntegrable N volume 0 (t+δ) :=
    normalTraceMixed_source_integrable hα hB hF hH0 hH htδ.le a ξ
  have hNt : IntervalIntegrable N volume 0 t := hNall.mono_set (by
    rw [uIcc_of_le ht.le,uIcc_of_le htδ.le]
    exact Icc_subset_Icc le_rfl hle)
  have hNtail : IntervalIntegrable N volume t (t+δ) := hNall.mono_set (by
    rw [uIcc_of_le hle,uIcc_of_le htδ.le]
    exact Icc_subset_Icc ht.le le_rfl)
  have hOi : IntervalIntegrable O volume 0 t :=
    normalTraceMixed_source_integrable hα hB hF hH0 hH ht.le a ξ
  have hAi : IntervalIntegrable A volume 0 t := hNt.sub hOi
  have harg (r : ℝ) : t+δ-(t-r) = r+δ := by abel
  have hKi : IntervalIntegrable K volume 0 t := by
    simpa only [K,A,N,O,sub_self,sub_zero,sub_sub_cancel,harg] using (hAi.comp_sub_left t).symm
  have hKa : (∫ r in (0 : ℝ)..t, K r) = ∫ σ in (0 : ℝ)..t, A σ := by
    simpa only [K,A,N,O,sub_self,sub_zero,sub_sub_cancel,harg] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := t) A t)
  have hSource (u : ℝ) : normalTraceMixed B u a ξ =
      ∫ σ in (0 : ℝ)..u, (2*normalGaussianKernel (u-σ) a) •
        fderiv ℝ (heatAverage (u-σ) (fun y => B (y,σ))) ξ := by
    simpa only [normalTraceMixed,sub_self,sub_zero,sub_sub_cancel] using
      (intervalIntegral.integral_comp_sub_left (a := (0 : ℝ)) (b := u)
        (fun r => (2*normalGaussianKernel r a) • fderiv ℝ (heatAverage r (fun y => B (y,u-r))) ξ) u).symm
  have heq : normalTraceMixed B (t+δ) a ξ-normalTraceMixed B t a ξ =
      (∫ r in (0 : ℝ)..t, K r)+(∫ σ in t..t+δ, N σ) := by
    rw [hSource (t+δ),hSource t]
    change (∫ σ in (0 : ℝ)..t+δ, N σ)-(∫ σ in (0 : ℝ)..t, O σ) = _
    rw [← intervalIntegral.integral_add_adjacent_intervals hNt hNtail,hKa]
    change _ = (∫ σ in (0 : ℝ)..t, N σ-O σ)+_
    rw [intervalIntegral.integral_sub hNt hOi]
    abel
  have hWeighted (r : ℝ) (hr : 0 < r) (σ : ℝ) :
      ‖(2*normalGaussianKernel r a) • fderiv ℝ (heatAverage r (fun y => B (y,σ))) ξ‖ ≤
        C2*H*r^(α/2-1) := by
    simpa only [add_sub_cancel_right] using hMixed B F H hB hF hH0 hH r hr (σ+r) a ξ
  have hnear (r : ℝ) (hr : r ∈ Ioc 0 t) : ‖K r‖ ≤ (2*C2*H)*r^(α/2-1) := by
    have hp : (r+δ)^(α/2-1) ≤ r^(α/2-1) :=
      Real.rpow_le_rpow_of_nonpos hr.1 (le_add_of_nonneg_right hδ.le) (by linarith)
    calc
      _ ≤ ‖(2*normalGaussianKernel (r+δ) a) • fderiv ℝ (heatAverage (r+δ) (fun y => B (y,t-r))) ξ‖ +
        ‖(2*normalGaussianKernel r a) • fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ‖ := norm_sub_le _ _
      _ ≤ C2*H*(r+δ)^(α/2-1)+C2*H*r^(α/2-1) :=
        add_le_add (hWeighted (r+δ) (add_pos hr.1 hδ) (t-r)) (hWeighted r hr.1 (t-r))
      _ ≤ C2*H*r^(α/2-1)+C2*H*r^(α/2-1) :=
        add_le_add (mul_le_mul_of_nonneg_left hp (by positivity)) le_rfl
      _ = _ := by ring
  have hfar (r : ℝ) (hr : r ∈ Ioc δ t) : ‖K r‖ ≤ (C4*H)*δ*r^(α/2-2) := by
    have hr0 : 0 < r := hδ.trans hr.1
    let J := fderiv ℝ (heatAverage r (fun y => B (y,t-r))) ξ
    let J' := fderiv ℝ (heatAverage (r+δ) (fun y => B (y,t-r))) ξ
    have hK : K r = (2*normalGaussianKernel (r+δ) a) • (J'-J)+
        (2*normalGaussianKernel (r+δ) a-2*normalGaussianKernel r a) • J := by
      dsimp only [K,J,J']; simp only [smul_sub,sub_smul]; abel
    have hg0 : 0 ≤ 2*normalGaussianKernel (r+δ) a :=
      mul_nonneg (by norm_num) (normalGaussianKernel_pos (add_pos hr0 hδ) a).le
    have hg : 2*normalGaussianKernel (r+δ) a ≤ Ck*r^(-(1/2 : ℝ)) := by
      have hh := mul_le_mul_of_nonneg_left
        (normalGaussianKernel_le_rpow (add_pos hr0 hδ) a) (by norm_num : (0:ℝ) ≤ 2)
      have hp : (r+δ)^(-(1/2 : ℝ)) ≤ r^(-(1/2 : ℝ)) :=
        Real.rpow_le_rpow_of_nonpos hr0 (le_add_of_nonneg_right hδ.le) (by norm_num)
      have hh' : 2*normalGaussianKernel (r+δ) a ≤ Ck*(r+δ)^(-(1/2 : ℝ)) := by
        simpa only [Ck,mul_assoc] using hh
      exact hh'.trans (mul_le_mul_of_nonneg_left hp hCk.le)
    have hp1 : r^(-(1/2 : ℝ))*r^(α/2-3/2) = r^(α/2-2) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    have hp2 : r^(-(3/2 : ℝ))*r^(α/2-1/2) = r^(α/2-2) := by
      rw [← Real.rpow_add hr0]; congr 1; ring
    rw [hK]
    calc
      _ ≤ ‖(2*normalGaussianKernel (r+δ) a) • (J'-J)‖+
        ‖(2*normalGaussianKernel (r+δ) a-2*normalGaussianKernel r a) • J‖ := norm_add_le _ _
      _ = (2*normalGaussianKernel (r+δ) a)*‖J'-J‖+
        |2*normalGaussianKernel (r+δ) a-2*normalGaussianKernel r a| *‖J‖ := by
          rw [norm_smul,norm_smul,Real.norm_eq_abs,Real.norm_eq_abs,abs_of_nonneg hg0]
      _ ≤ (Ck*r^(-(1/2 : ℝ)))*(C3*H*δ*r^(α/2-3/2))+
          (Cp*δ*r^(-(3/2 : ℝ)))*(Cg*H*r^(α/2-1/2)) := add_le_add
        (mul_le_mul hg (hInc r hr0 δ hδ.le (fun y => B (y,t-r)) F H
          (hfc (t-r)) (hFs (t-r)) hH0 (hH (t-r)) ξ) (norm_nonneg _) (by positivity))
        (mul_le_mul (hProfile r hr0 δ hδ.le a ha)
          (hGrad r hr0 (fun y => B (y,t-r)) F H (hfc (t-r)) (hFs (t-r)) hH0 (hH (t-r)) ξ)
          (norm_nonneg _) (by positivity))
      _ = (Ck*C3)*H*δ*(r^(-(1/2 : ℝ))*r^(α/2-3/2))+
          (Cp*Cg)*H*δ*(r^(-(3/2 : ℝ))*r^(α/2-1/2)) := by ring
      _ = _ := by rw [hp1,hp2]; dsimp [C4]; ring
  have hOld := schauder_temporal_near_far_integral_bound hα (by linarith : α < 2)
    (by positivity : 0 ≤ 2*C2*H) (by positivity : 0 ≤ C4*H) hδ ht hKi hnear hfar
  have hPow : IntervalIntegrable (fun σ : ℝ => (t+δ-σ)^(α/2-1)) volume t (t+δ) :=
    (schauder_time_weight_integrable hα (t+δ)).mono_set (by
      rw [uIcc_of_le hle,uIcc_of_le htδ.le]
      exact Icc_subset_Icc ht.le le_rfl)
  have hTail := intervalIntegral.norm_integral_le_of_norm_le hle
    (f := N) (g := fun σ : ℝ => C2*H*(t+δ-σ)^(α/2-1))
    (by
      filter_upwards [(volume : Measure ℝ).ae_ne (t+δ)] with σ hσt
      intro hσ
      exact hWeighted (t+δ-σ) (sub_pos.mpr (lt_of_le_of_ne hσ.2 hσt)) σ)
    (hPow.const_mul (C2*H))
  have hTailWeight : (∫ σ in t..t+δ, (t+δ-σ)^(α/2-1)) = (2/α)*δ^(α/2) := by
    rw [intervalIntegral.integral_comp_sub_left (fun r : ℝ => r^(α/2-1)) (t+δ)]
    simp only [sub_self,add_sub_cancel_left]
    rw [integral_rpow (Or.inl (by linarith : -1 < α/2-1)),
      show α/2-1+1 = α/2 by ring,Real.zero_rpow (by positivity : α/2 ≠ 0),sub_zero]
    field_simp [hα.ne']
  rw [intervalIntegral.integral_const_mul,hTailWeight] at hTail
  rw [heq]
  calc
    _ ≤ ‖∫ r in (0 : ℝ)..t, K r‖+‖∫ σ in t..t+δ, N σ‖ := norm_add_le _ _
    _ ≤ (6*C2/α+2*C4/(2-α))*H*δ^(α/2) := by
      convert add_le_add hOld hTail using 1; ring
    _ ≤ C*H*δ^(α/2) := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hRestC hH0) (Real.rpow_nonneg hδ.le _)



/-- Joint three-direction Holder estimate for the actual operator-norm mixed integral.
The constant is chosen before the source and its budget. All three closed faces,
including initial time and zero height, are covered by the preceding estimates. -/
theorem normalTraceMixed_holder_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F : ℝ),
      HolderBound α Set.univ B F →
      ∀ (ξ η : Space n) (a b t s : ℝ), 0 ≤ a → 0 ≤ b →
        t ∈ Icc 0 1 → s ∈ Icc 0 1 →
        ‖normalTraceMixed B t a ξ-normalTraceMixed B s b η‖ ≤
          C*F*(‖ξ-η‖^α+|a-b|^α+|t-s|^(α/2)) := by
  obtain ⟨Cs,hCs,hSpace⟩ := normalTraceMixed_spatial_holder_bound (n := n) hα hα1
  obtain ⟨Ca,hCa,hNormal⟩ := normalTraceMixed_normal_holder_bound (n := n) hα hα1
  obtain ⟨Ct,hCt,hTime⟩ := normalTraceMixed_temporal_holder_bound (n := n) hα hα1
  let C : ℝ := Cs+Ca+Ct
  have hC : 0 < C := by dsimp [C]; positivity
  have hCsC : Cs ≤ C := by dsimp [C]; linarith
  have hCaC : Ca ≤ C := by dsimp [C]; linarith
  have hCtC : Ct ≤ C := by dsimp [C]; linarith
  refine ⟨C,hC,?_⟩
  intro B F hB ξ η a b t s ha hb ht hs
  have hBc : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hBF (p : Point n) : |B p| ≤ F := by
    simpa only [Real.norm_eq_abs] using hB.2.1 p (mem_univ _)
  have hBH (σ : ℝ) (x y : Space n) : |B (x,σ)-B (y,σ)| ≤ F*‖x-y‖^α := by
    simpa only [holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero,Real.norm_eq_abs] using
      hB.2.2 (x,σ) (mem_univ _) (y,σ) (mem_univ _)
  have htime : ‖normalTraceMixed B t b η-normalTraceMixed B s b η‖ ≤
      Ct*F*|t-s|^(α/2) := by
    rcases le_total s t with hst | hts
    · have hh := hTime B F F hBc hBF hB.1 hBH s (t-s) b hs.1 (sub_nonneg.mpr hst) hb η
      rw [show s+(t-s) = t by ring] at hh
      simpa only [abs_of_nonneg (sub_nonneg.mpr hst)] using hh
    · have hh := hTime B F F hBc hBF hB.1 hBH t (s-t) b ht.1 (sub_nonneg.mpr hts) hb η
      rw [show t+(s-t) = s by ring] at hh
      rw [norm_sub_rev,abs_sub_comm]
      simpa only [abs_of_nonneg (sub_nonneg.mpr hts)] using hh
  calc
    _ = ‖(normalTraceMixed B t a ξ-normalTraceMixed B t a η)+
        (normalTraceMixed B t a η-normalTraceMixed B t b η)+
        (normalTraceMixed B t b η-normalTraceMixed B s b η)‖ := by
          congr 1; abel
    _ ≤ ‖normalTraceMixed B t a ξ-normalTraceMixed B t a η‖+
        ‖normalTraceMixed B t a η-normalTraceMixed B t b η‖+
        ‖normalTraceMixed B t b η-normalTraceMixed B s b η‖ := norm_add₃_le
    _ ≤ Cs*F*‖ξ-η‖^α+Ca*F*|a-b|^α+Ct*F*|t-s|^(α/2) :=
      add_le_add (add_le_add
        (hSpace B F F hBc hBF hB.1 hBH t a ht.1 ξ η)
        (hNormal B F F hBc hBF hB.1 hBH t a b ht.1 ha hb η)) htime
    _ ≤ C*F*‖ξ-η‖^α+C*F*|a-b|^α+C*F*|t-s|^(α/2) :=
      add_le_add (add_le_add
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCsC hB.1)
          (Real.rpow_nonneg (norm_nonneg _) _))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCaC hB.1)
          (Real.rpow_nonneg (abs_nonneg _) _)))
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hCtC hB.1)
          (Real.rpow_nonneg (abs_nonneg _) _))
    _ = _ := by ring

end Yau.LeafProofs.L16Aux
