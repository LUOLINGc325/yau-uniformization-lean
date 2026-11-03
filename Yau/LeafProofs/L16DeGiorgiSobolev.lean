import Yau.LeafProofs.L16DeGiorgiTruncation
import Yau.LeafProofs.L09
import Mathlib.Analysis.FunctionalSpaces.SobolevInequality

open MeasureTheory Filter Set
open scoped Topology ContDiff NNReal ENNReal
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance dgSobolev_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance dgSobolev_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance

/-- The actual coordinate gradient has the Hilbert dual norm, in real dimension 2n. -/
theorem dg_fderiv_norm_sq {n : ℕ} (g : Space n → ℝ) (x : Space n) :
    ‖fderiv ℝ g x‖^2 = dgGradientSq (fun i => d g x i) := by
  simpa only [dgGradientSq,d,complexVector_realOrthonormalBasis_apply] using
    (complexVector_realOrthonormalBasis n).norm_dual (fderiv ℝ g x)

/-- Squaring a finite norm gives its precise real integral power. -/
theorem dg_lpNorm_nnreal_sq {E : Type*} [NormedAddCommGroup E] {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {g : X → E} {p : ℝ≥0}
    (hp : p ≠ 0) (hg : MemLp g p μ) :
    (lpNorm g p μ)^2 = (∫ x, ‖g x‖^(p:ℝ) ∂μ)^(2/(p:ℝ)) := by
  rw [lpNorm_nnreal_eq_integral_norm_rpow hp hg.aestronglyMeasurable]
  calc
    _ = ((∫ x, ‖g x‖^(p:ℝ) ∂μ)^((p:ℝ)⁻¹))^(2:ℝ) := (Real.rpow_two _).symm
    _ = (∫ x, ‖g x‖^(p:ℝ) ∂μ)^((p:ℝ)⁻¹*2) :=
      (Real.rpow_mul (integral_nonneg fun x => Real.rpow_nonneg (norm_nonneg _) _) _ _).symm
    _ = _ := by congr 1; ring

/-- A finite L2 norm squares to the honest quadratic integral. -/
theorem dg_lpNorm_two_sq {E : Type*} [NormedAddCommGroup E] {X : Type*}
    [MeasurableSpace X] {μ : Measure X} {g : X → E} (hg : MemLp g 2 μ) :
    (lpNorm g 2 μ)^2 = ∫ x, ‖g x‖^2 ∂μ := by
  convert dg_lpNorm_nnreal_sq (p := (2:ℝ≥0)) (by norm_num) hg using 1 <;> norm_num

/-- The high-dimensional first-gradient L2 Sobolev inequality. Its constant
is fixed before the function; no higher jet is an input or appears on the right. -/
theorem dg_spatial_sobolev_two {n : ℕ} (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Space n → ℝ,
      ContDiff ℝ 1 z → HasCompactSupport z →
      (∫ x, |z x|^((2:ℝ)*n/(n-1)))^(((n:ℝ)-1)/n) ≤
        C*(∫ x, dgGradientSq (fun i => d z x i)) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  let p : ℝ≥0 := ⟨2*(n:ℝ)/((n:ℝ)-1),by positivity⟩
  let c : ℝ≥0 := eLpNormLESNormFDerivOfEqInnerConst (volume : Measure (Space n)) 2
  refine ⟨(c:ℝ)^2+1,by positivity,?_⟩
  intro z hz hcz
  have hp0 : 0 < p := by change (0:ℝ) < 2*(n:ℝ)/((n:ℝ)-1); positivity
  have hzLp : MemLp z (p : ℝ≥0∞) volume := hz.continuous.memLp_of_hasCompactSupport hcz
  have hDzLp : MemLp (fderiv ℝ z) 2 volume :=
    (hz.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hcz.fderiv ℝ)
  have hdim : 0 < Module.finrank ℝ (Space n) := by
    rw [complexVector_finrank_real]; omega
  have he : (p:ℝ)⁻¹ = (2:ℝ)⁻¹-(Module.finrank ℝ (Space n):ℝ)⁻¹ := by
    rw [complexVector_finrank_real]
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    change (2*(n:ℝ)/((n:ℝ)-1))⁻¹ = (2:ℝ)⁻¹-((2:ℝ)*n)⁻¹
    field_simp
  have h := eLpNorm_le_eLpNorm_fderiv_of_eq_inner (volume : Measure (Space n))
    hz hcz (p := (2:ℝ≥0)) (p' := p) (by norm_num) hdim he
  have hReal := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hDzLp.eLpNorm_ne_top) h
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal] at hReal
  change lpNorm z p volume ≤ (c:ℝ)*lpNorm (fderiv ℝ z) 2 volume at hReal
  have hsq := (sq_le_sq₀ (by exact ENNReal.toReal_nonneg : 0 ≤ lpNorm z p volume)
    (mul_nonneg c.coe_nonneg ENNReal.toReal_nonneg)).mpr hReal
  change (lpNorm z p volume)^2 ≤ ((c:ℝ)*lpNorm (fderiv ℝ z) 2 volume)^2 at hsq
  have hleft : (lpNorm z p volume)^2 =
      (∫ x, |z x|^((2:ℝ)*n/(n-1)))^(((n:ℝ)-1)/n) := by
    rw [dg_lpNorm_nnreal_sq hp0.ne' hzLp]
    simp only [Real.norm_eq_abs]
    change (∫ x, |z x|^((2:ℝ)*n/(n-1)))^(2/(2*(n:ℝ)/((n:ℝ)-1))) = _
    congr 1
    field_simp
  rw [hleft,mul_pow,dg_lpNorm_two_sq hDzLp] at hsq
  have hgrad : (∫ x, ‖fderiv ℝ z x‖^2) = ∫ x, dgGradientSq (fun i => d z x i) := by
    simp_rw [dg_fderiv_norm_sq]
  rw [hgrad] at hsq
  exact hsq.trans (mul_le_mul_of_nonneg_right (by linarith : (c:ℝ)^2 ≤ (c:ℝ)^2+1)
    (integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _))


/-- The two-dimensional first-gradient inequality, with its explicit L4 exponent. -/
theorem dg_spatial_sobolev_dimension_two :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Space 1 → ℝ,
      ContDiff ℝ 1 z → HasCompactSupport z →
      (∫ x, |z x|^4) ≤ C*(∫ x, (z x)^2)*(∫ x, dgGradientSq (fun i => d z x i)) := by
  let c : ℝ≥0 := eLpNormLESNormFDerivOneConst (volume : Measure (Space 1)) 2
  refine ⟨4*(c:ℝ)^2+1,by positivity,?_⟩
  intro z hz hcz
  have hzLp : MemLp z 2 volume := hz.continuous.memLp_of_hasCompactSupport hcz
  have hDzLp : MemLp (fderiv ℝ z) 2 volume :=
    (hz.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hcz.fderiv ℝ)
  have hz2 : ContDiff ℝ 1 (fun x => (z x)^2) := hz.pow 2
  have hcz2 : HasCompactSupport (fun x => (z x)^2) := by
    simpa only [Function.comp_def] using hcz.comp_left (g := fun r : ℝ => r^2) (by simp)
  have hz2Lp : MemLp (fun x => (z x)^2) 2 volume := hz2.continuous.memLp_of_hasCompactSupport hcz2
  have hDz2Lp : MemLp (fderiv ℝ (fun x => (z x)^2)) 1 volume :=
    (hz2.continuous_fderiv (by simp)).memLp_of_hasCompactSupport (hcz2.fderiv ℝ)
  have hp : NNReal.HolderConjugate (Module.finrank ℝ (Space 1)) 2 := by
    simpa only [complexVector_finrank_real, mul_one, Nat.cast_ofNat] using NNReal.HolderConjugate.two_two
  have hSob := eLpNorm_le_eLpNorm_fderiv_one (volume : Measure (Space 1)) hz2 hcz2 hp
  have hr := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.coe_ne_top hDz2Lp.eLpNorm_ne_top) hSob
  simp only [ENNReal.toReal_mul,ENNReal.coe_toReal] at hr
  change lpNorm (fun x => (z x)^2) 2 volume ≤ (c:ℝ)*lpNorm (fderiv ℝ (fun x => (z x)^2)) 1 volume at hr
  rw [lpNorm_one_eq_integral_norm hDz2Lp.aestronglyMeasurable] at hr
  have hprodI : Integrable (fun x => |z x| *‖fderiv ℝ z x‖) := by
    have hh : Integrable (fun x : Space 1 => ‖z x‖*‖fderiv ℝ z x‖) volume := ((hz.continuous.norm).mul (hz.continuous_fderiv (by simp)).norm).integrable_of_hasCompactSupport
      hcz.norm.mul_right
    simpa only [Real.norm_eq_abs] using hh
  have hD2I : Integrable (fderiv ℝ (fun x => (z x)^2)) volume :=
    (hz2.continuous_fderiv (by simp)).integrable_of_hasCompactSupport (hcz2.fderiv ℝ)
  have hprod : (∫ x, ‖fderiv ℝ (fun y => (z y)^2) x‖) ≤ 2*(∫ x, |z x| *‖fderiv ℝ z x‖) := by
    rw [← integral_const_mul]
    apply integral_mono hD2I.norm (hprodI.const_mul 2)
    intro x
    change ‖fderiv ℝ (fun y => (z y)^2) x‖ ≤ 2*(|z x| *‖fderiv ℝ z x‖)
    rw [fderiv_fun_pow 2 (hz.differentiable (by simp) x),norm_smul,Real.norm_eq_abs]
    norm_num [nsmul_eq_mul,abs_mul]
    nlinarith
  have hCS := integral_mul_norm_le_Lp_mul_Lq (f := z) (g := fun x => ‖fderiv ℝ z x‖) Real.HolderConjugate.two_two
    (by simpa using hzLp) (by simpa using hDzLp.norm)
  have hCS' : (∫ x, |z x| *‖fderiv ℝ z x‖) ≤
      (∫ x, (z x)^2)^(1/2:ℝ)*(∫ x, ‖fderiv ℝ z x‖^2)^(1/2:ℝ) := by
    simpa only [Real.norm_eq_abs,abs_of_nonneg (norm_nonneg _),Real.rpow_two,sq_abs] using hCS
  have hroot : lpNorm (fun x => (z x)^2) 2 volume ≤
      (2*(c:ℝ))*(∫ x, (z x)^2)^(1/2:ℝ)*(∫ x, ‖fderiv ℝ z x‖^2)^(1/2:ℝ) := by
    calc
      _ ≤ (c:ℝ)*(2*(∫ x, |z x| *‖fderiv ℝ z x‖)) := hr.trans (mul_le_mul_of_nonneg_left hprod c.coe_nonneg)
      _ ≤ (c:ℝ)*(2*((∫ x, (z x)^2)^(1/2:ℝ)*(∫ x, ‖fderiv ℝ z x‖^2)^(1/2:ℝ))) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hCS' (by norm_num)) c.coe_nonneg
      _ = _ := by ring
  have hsq := (sq_le_sq₀ (lpNorm_nonneg (f := fun x => (z x)^2)) (by positivity)).mpr hroot
  change (lpNorm (fun x => (z x)^2) 2 volume)^2 ≤
    ((2*(c:ℝ))*(∫ x, (z x)^2)^(1/2:ℝ)*(∫ x, ‖fderiv ℝ z x‖^2)^(1/2:ℝ))^2 at hsq
  rw [dg_lpNorm_two_sq hz2Lp] at hsq
  have hhalf1 : ((∫ x, (z x)^2)^(1/2:ℝ))^2 = ∫ x, (z x)^2 := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  have hhalf2 : ((∫ x, ‖fderiv ℝ z x‖^2)^(1/2:ℝ))^2 = ∫ x, ‖fderiv ℝ z x‖^2 := by
    rw [← Real.sqrt_eq_rpow]; exact Real.sq_sqrt (integral_nonneg fun _ => sq_nonneg _)
  simp only [mul_pow,hhalf1,hhalf2] at hsq
  have hleft : (∫ x, ‖(z x)^2‖^2) = ∫ x, |z x|^4 := by
    congr 1; funext x; rw [Real.norm_eq_abs,abs_pow]; ring
  rw [hleft] at hsq
  simp_rw [dg_fderiv_norm_sq] at hsq
  have hnonneg : 0 ≤ (∫ x, (z x)^2)*(∫ x, dgGradientSq (fun i => d z x i)) := by
    apply mul_nonneg (integral_nonneg fun _ => sq_nonneg _)
    exact integral_nonneg fun x => Finset.sum_nonneg fun i _ => sq_nonneg _
  calc
    _ ≤ (4*(c:ℝ)^2)*((∫ x, (z x)^2)*(∫ x, dgGradientSq (fun i => d z x i))) := by
      convert hsq using 1; ring
    _ ≤ (4*(c:ℝ)^2+1)*((∫ x, (z x)^2)*(∫ x, dgGradientSq (fun i => d z x i))) :=
      mul_le_mul_of_nonneg_right (by linarith) hnonneg
    _ = _ := by ring


/-- Compact support and continuity give all finite power integrability used below. -/
theorem dg_abs_rpow_memLp {n : ℕ} {z : Space n → ℝ} (hz : Continuous z)
    (hcz : HasCompactSupport z) {r : ℝ} (hr : 0 < r) (p : ℝ≥0∞) :
    MemLp (fun x => |z x|^r) p volume := by
  have hc : Continuous (fun x => |z x|^r) := (Real.continuous_rpow_const hr.le).comp hz.abs
  have hcs : HasCompactSupport (fun x => |z x|^r) := by
    simpa only [Function.comp_def] using
      hcz.comp_left (g := fun y : ℝ => |y|^r) (by rw [abs_zero,Real.zero_rpow hr.ne'])
  exact hc.memLp_of_hasCompactSupport hcs

/-- Spatial interpolation in every higher even dimension uses only first gradients. -/
theorem dg_spatial_parabolic_sobolev_high {n : ℕ} (hn : 1 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Space n → ℝ,
      ContDiff ℝ 1 z → HasCompactSupport z →
      (∫ x, |z x|^((2:ℝ)+2/n)) ≤
        C*(∫ x, (z x)^2)^((n:ℝ)⁻¹)*(∫ x, dgGradientSq (fun i => d z x i)) := by
  obtain ⟨C,hC,hS⟩ := dg_spatial_sobolev_two hn
  refine ⟨C,hC,?_⟩
  intro z hz hcz
  have hn0 : (0 : ℝ) < n := by exact_mod_cast (Nat.zero_lt_of_lt hn)
  have hn1 : (1 : ℝ) < n := by exact_mod_cast hn
  have hconj : Real.HolderConjugate (n:ℝ) ((n:ℝ)/(n-1)) := by
    apply Real.holderConjugate_iff.mpr
    refine ⟨hn1,?_⟩
    field_simp
    ring
  have hf := dg_abs_rpow_memLp hz.continuous hcz (by positivity : 0 < (2:ℝ)/n) (ENNReal.ofReal n)
  have hg := dg_abs_rpow_memLp hz.continuous hcz (by norm_num : (0:ℝ) < 2) (ENNReal.ofReal ((n:ℝ)/(n-1)))
  have hHolder := integral_mul_le_Lp_mul_Lq_of_nonneg hconj
    (f := fun x => |z x|^((2:ℝ)/n)) (g := fun x => |z x|^(2:ℝ))
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _)
    (ae_of_all _ fun x => Real.rpow_nonneg (abs_nonneg _) _) hf hg
  have hprod : (∫ x, |z x|^((2:ℝ)/n)*|z x|^(2:ℝ)) = ∫ x, |z x|^((2:ℝ)+2/n) := by
    congr 1; funext x
    rw [← Real.rpow_add_of_nonneg (abs_nonneg _) (by positivity : 0 ≤ (2:ℝ)/n) (by norm_num)]
    congr 1; ring
  have hF : (∫ x, (|z x|^((2:ℝ)/n))^(n:ℝ)) = ∫ x, (z x)^2 := by
    congr 1; funext x
    rw [← Real.rpow_mul (abs_nonneg _),show ((2:ℝ)/n)*(n:ℝ) = 2 by field_simp,Real.rpow_two,sq_abs]
  have hG : (∫ x, (|z x|^(2:ℝ))^((n:ℝ)/(n-1))) = ∫ x, |z x|^((2:ℝ)*n/(n-1)) := by
    congr 1; funext x
    rw [← Real.rpow_mul (abs_nonneg _)]
    congr 1; ring
  have he : (1 / ((n:ℝ)/(n-1))) = ((n:ℝ)-1)/n := by field_simp
  rw [hprod,hF,hG,he,one_div] at hHolder
  calc
    _ ≤ (∫ x, (z x)^2)^((n:ℝ)⁻¹)*(∫ x, |z x|^((2:ℝ)*n/(n-1)))^(((n:ℝ)-1)/n) := hHolder
    _ ≤ (∫ x, (z x)^2)^((n:ℝ)⁻¹)*(C*(∫ x, dgGradientSq (fun i => d z x i))) :=
      mul_le_mul_of_nonneg_left (hS z hz hcz) (Real.rpow_nonneg (integral_nonneg fun _ => sq_nonneg _) _)
    _ = _ := by ring

/-- First-gradient spatial Gagliardo--Nirenberg in actual real dimension d=2n.
The dimension-two endpoint uses the separate explicit L4 proof above. -/
theorem dg_spatial_parabolic_sobolev {n : ℕ} (hn : 0 < n) :
    ∃ C : ℝ, 0 < C ∧ ∀ z : Space n → ℝ,
      ContDiff ℝ 1 z → HasCompactSupport z →
      (∫ x, |z x|^((2:ℝ)+2/n)) ≤
        C*(∫ x, (z x)^2)^((n:ℝ)⁻¹)*(∫ x, dgGradientSq (fun i => d z x i)) := by
  by_cases hn1 : n = 1
  · subst n
    obtain ⟨C,hC,hS⟩ := dg_spatial_sobolev_dimension_two
    refine ⟨C,hC,?_⟩
    intro z hz hcz
    simpa only [Nat.cast_one,div_one,show (2:ℝ)+2 = 4 by norm_num,
      Real.rpow_ofNat,inv_one,Real.rpow_one] using hS z hz hcz
  · exact dg_spatial_parabolic_sobolev_high (by omega)


theorem dg_segment_integral {n : ℕ}
    {O : Set (Space n)} (hO : IsOpen O) (hconv : Convex ℝ O) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 1 u O) {x y : Space n} (hx : x ∈ O) (hy : y ∈ O) :
    u y - u x = ∫ t : ℝ in 0..1,
      fderiv ℝ u (x + t • (y - x)) (y - x) := by
  let p : ℝ → Space n := fun t => x + t • (y - x)
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : p t ∈ O :=
    hconv.add_smul_sub_mem hx hy ht
  have hDc : ContinuousOn (fun t => fderiv ℝ u (p t) (y - x)) (Set.Icc (0 : ℝ) 1) := by
    apply ContinuousOn.clm_apply _ continuousOn_const
    exact (hu.continuousOn_fderiv_of_isOpen hO (by simp)).comp
      (by dsimp [p]; fun_prop) hp
  have hderiv (t : ℝ) (ht : t ∈ Set.uIcc (0 : ℝ) 1) :
      HasDerivAt (fun t => u (p t)) (fderiv ℝ u (p t) (y - x)) t := by
    have hpt : p t ∈ O := hp t (by simpa using ht)
    have hup := (hu.contDiffAt (hO.mem_nhds hpt)).differentiableAt (by simp)
    apply hup.hasFDerivAt.comp_hasDerivAt t
    simpa [p] using (((hasDerivAt_id t).smul_const (y - x)).const_add x)
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
    (hDc.intervalIntegrable_of_Icc zero_le_one)
  simpa [p] using h.symm

theorem dg_segment_norm_le {n : ℕ}
    {O : Set (Space n)} (hO : IsOpen O) (hconv : Convex ℝ O) {u : Space n → ℝ}
    (hu : ContDiffOn ℝ 1 u O) {x y : Space n} (hx : x ∈ O) (hy : y ∈ O) :
    |u y - u x| ≤ ∫ t : ℝ in 0..1,
      ‖fderiv ℝ u (x + t • (y - x))‖ * ‖y - x‖ := by
  have hp (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) 1) : x + t • (y - x) ∈ O :=
    hconv.add_smul_sub_mem hx hy ht
  have hD : ContinuousOn (fun t : ℝ => fderiv ℝ u (x + t • (y - x))) (Set.Icc 0 1) :=
    (hu.continuousOn_fderiv_of_isOpen hO (by simp)).comp (by fun_prop) hp
  rw [dg_segment_integral hO hconv hu hx hy, ← Real.norm_eq_abs]
  apply (intervalIntegral.norm_integral_le_integral_norm zero_le_one).trans
  apply intervalIntegral.integral_mono_on zero_le_one
    ((hD.clm_apply continuousOn_const).norm.intervalIntegrable_of_Icc zero_le_one)
    ((hD.norm.mul continuousOn_const).intervalIntegrable_of_Icc zero_le_one)
  intro t _
  exact (fderiv ℝ u (x + t • (y - x))).le_opNorm (y - x)

theorem dg_segment_ball_integral_le {n : ℕ}
    {c x : Space n} {R t : ℝ} (hx : x ∈ Metric.ball c R) (ht : 0 < t) (ht1 : t ≤ 1)
    {h : Space n → ℝ} (hi : IntegrableOn h (Metric.ball c R) volume)
    (hnonneg : ∀ y ∈ Metric.ball c R, 0 ≤ h y) :
    (∫ y in Metric.ball c R, h (x + t • (y - x))) ≤
      (t ^ (2*n))⁻¹ * (∫ y in Metric.ball c R, h y) := by
  classical
  let H : Space n → ℝ := (Metric.ball c R).indicator h
  have hH : Integrable H := (integrable_indicator_iff measurableSet_ball).mpr hi
  have hHnonneg (y : Space n) : 0 ≤ H y := by
    dsimp [H]
    exact Set.indicator_nonneg (fun z hz => hnonneg z hz) y
  have hcomp : Integrable (fun y => H (x + t • (y - x))) := by
    simpa only [sub_eq_add_neg] using ((hH.comp_add_left x).comp_smul ht.ne').comp_add_right (-x)
  calc
    _ = ∫ y in Metric.ball c R, H (x + t • (y - x)) := by
      apply setIntegral_congr_fun measurableSet_ball
      intro y hy
      dsimp only [H]
      rw [Set.indicator_of_mem ((convex_ball c R).add_smul_sub_mem hx hy ⟨ht.le, ht1⟩)]
    _ ≤ ∫ y : Space n, H (x + t • (y - x)) :=
      integral_mono_measure Measure.restrict_le_self (Filter.Eventually.of_forall fun _ => hHnonneg _)
        hcomp
    _ = ∫ y : Space n, H (x + t • y) := by
      simpa only [sub_eq_add_neg] using
        integral_add_right_eq_self (fun y : Space n => H (x + t • y)) (-x)
    _ = (t ^ (2*n))⁻¹ * (∫ y : Space n, H (x + y)) := by
      simpa only [complexVector_finrank_real, abs_of_nonneg (inv_nonneg.mpr (pow_nonneg ht.le _)),
        smul_eq_mul] using Measure.integral_comp_smul (volume : Measure (Space n)) (fun y => H (x + y)) t
    _ = _ := by
      rw [integral_add_left_eq_self, integral_indicator measurableSet_ball]


/-- Half-segments have a dimension-only Jacobian bound. -/
theorem dg_segment_ball_integral_le_half {n : ℕ} {c x : Space n} {R t : ℝ}
    (hx : x ∈ Metric.ball c R) (ht : t ∈ Icc (1/2 : ℝ) 1)
    {h : Space n → ℝ} (hi : IntegrableOn h (Metric.ball c R) volume)
    (hnonneg : ∀ y ∈ Metric.ball c R, 0 ≤ h y) :
    (∫ y in Metric.ball c R, h (x+t • (y-x))) ≤
      (2:ℝ)^(2*n)*(∫ y in Metric.ball c R, h y) := by
  have ht0 : 0 < t := lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/2) ht.1
  have hpow : (t^(2*n))⁻¹ ≤ (2:ℝ)^(2*n) := by
    calc
      _ ≤ (((1/2 : ℝ)^(2*n))⁻¹) := inv_anti₀ (by positivity)
        (pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) ht.1 _)
      _ = _ := by simp [inv_pow]
  have hInt : 0 ≤ ∫ y in Metric.ball c R, h y := by
    apply integral_nonneg_of_ae
    filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
    exact hnonneg y hy
  exact (dg_segment_ball_integral_le hx ht0 ht.2 hi hnonneg).trans
    (mul_le_mul_of_nonneg_right hpow hInt)


/-- The elementary product-gradient bound used to dominate genuine smooth truncations. -/
theorem dg_cutoff_linear_norm_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (p v β θ : ℝ) (D H : E) (hβ : 0 ≤ β ∧ β ≤ v) (hθ : 0 ≤ θ ∧ θ ≤ 1) :
    ‖p • (θ • D)+β • H‖^2 ≤ 2*p^2*‖D‖^2+2*v^2*‖H‖^2 := by
  have hv : 0 ≤ v := hβ.1.trans hβ.2
  have hb : ‖p • (θ • D)+β • H‖ ≤ |p| *‖D‖+v*‖H‖ := by
    calc
      _ ≤ ‖p • (θ • D)‖+‖β • H‖ := norm_add_le _ _
      _ = |p| *(θ*‖D‖)+β*‖H‖ := by
        simp only [norm_smul,Real.norm_eq_abs,abs_of_nonneg hθ.1,abs_of_nonneg hβ.1]
      _ ≤ |p| *‖D‖+v*‖H‖ := add_le_add
        (mul_le_mul_of_nonneg_left (mul_le_of_le_one_left (norm_nonneg _) hθ.2) (abs_nonneg _))
        (mul_le_mul_of_nonneg_right hβ.2 (norm_nonneg _))
  calc
    _ ≤ (|p| *‖D‖+v*‖H‖)^2 := (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hb
    _ ≤ 2*(|p| *‖D‖)^2+2*(v*‖H‖)^2 := by nlinarith [sq_nonneg (|p| *‖D‖-v*‖H‖)]
    _ = _ := by simp only [mul_pow,sq_abs]; ring

/-- Spatial first-gradient Sobolev for the actual positive part times a smooth
cutoff. The nonsmooth level is retained by the one-sided smooth approximation. -/
theorem dg_spatial_positivePart_sobolev_global {n : ℕ} (hn : 0 < n) :
    ∃ S : ℝ, 0 < S ∧ ∀ (w φ : Space n → ℝ),
      ContDiff ℝ ∞ w → ContDiff ℝ ∞ φ → HasCompactSupport φ →
      let v : Space n → ℝ := fun x => dgPositivePart (w x)
      let G : Space n → Space n →L[ℝ] ℝ := fun x =>
        φ x • (if 0 < w x then fderiv ℝ w x else 0)+v x • fderiv ℝ φ x
      Integrable (fun x => |v x*φ x|^((2:ℝ)+2/n)) volume ∧
      Integrable (fun x => (v x*φ x)^2) volume ∧
      Integrable (fun x => ‖G x‖^2) volume ∧
      (∫ x, |v x*φ x|^((2:ℝ)+2/n)) ≤ S*(∫ x, (v x*φ x)^2)^((n:ℝ)⁻¹)*(∫ x, ‖G x‖^2) := by
  obtain ⟨S,hS,hGN⟩ := dg_spatial_parabolic_sobolev hn
  refine ⟨S,hS,?_⟩
  intro w φ hw hφ hcφ
  let v : Space n → ℝ := fun x => dgPositivePart (w x)
  let G : Space n → Space n →L[ℝ] ℝ := fun x =>
    φ x • (if 0 < w x then fderiv ℝ w x else 0)+v x • fderiv ℝ φ x
  let q : ℝ := 2+2/(n:ℝ)
  have hn0 : (0:ℝ) < n := by exact_mod_cast hn
  have hq : 0 < q := by dsimp [q]; positivity
  let ε : ℕ → ℝ := fun j => 1/((j:ℝ)+1)
  have hε : ∀ j, 0 < ε j := by intro j; dsimp [ε]; positivity
  have hεlim : Tendsto ε atTop (𝓝 0) := tendsto_one_div_add_atTop_nhds_zero_nat
  let z : ℕ → Space n → ℝ := fun j x => dgSmoothPos (ε j) (w x)*φ x
  have hz (j : ℕ) : ContDiff ℝ ∞ (z j) := ((dgSmoothPos_contDiff (ε j)).comp hw).mul hφ
  have hcz (j : ℕ) : HasCompactSupport (z j) := hcφ.mul_left
  have hdz (j : ℕ) (x : Space n) : fderiv ℝ (z j) x =
      φ x • (dgSmoothStep (ε j) (w x) • fderiv ℝ w x)+
        dgSmoothPos (ε j) (w x) • fderiv ℝ φ x := by
    have hb := HasDerivAt.comp_hasFDerivAt x (dgSmoothPos_hasDerivAt (ε j) (w x))
      (hw.differentiable (by simp) x).hasFDerivAt
    have hd := hb.mul (hφ.differentiable (by simp) x).hasFDerivAt
    simpa only [z,Function.comp_def,Pi.mul_def,add_comm] using hd.fderiv
  have hv : Continuous v := dgPositivePart_lipschitz.continuous.comp hw.continuous
  have hv0 (x : Space n) : 0 ≤ v x := dgPositivePart_nonneg _
  have hvc : HasCompactSupport (fun x => v x*φ x) := hcφ.mul_left
  have hVI (r : ℝ) (hr : 0 < r) : Integrable (fun x => |v x*φ x|^r) volume := by
    exact memLp_one_iff_integrable.mp (dg_abs_rpow_memLp (hv.mul hφ.continuous) hvc hr 1)
  have hAI : Integrable (fun x => |v x*φ x|^q) volume := hVI q hq
  have hBI : Integrable (fun x => (v x*φ x)^2) volume := by
    simpa only [Real.rpow_two,sq_abs] using hVI 2 (by norm_num)
  let F : Space n → ℝ := fun x => 2*(φ x)^2*‖fderiv ℝ w x‖^2+2*(v x)^2*‖fderiv ℝ φ x‖^2
  have hFC : Continuous F := by
    have hDCw : Continuous (fun x => ‖fderiv ℝ w x‖^2) := (hw.continuous_fderiv (by simp)).norm.pow 2
    have hDCφ : Continuous (fun x => ‖fderiv ℝ φ x‖^2) := (hφ.continuous_fderiv (by simp)).norm.pow 2
    exact ((continuous_const.mul (hφ.continuous.pow 2)).mul hDCw).add
      ((continuous_const.mul (hv.pow 2)).mul hDCφ)
  have hFI : Integrable F volume := by
    have hh := dg_integrable_spatial isOpen_univ hcφ (subset_univ _) hFC.continuousOn (by
      intro x _ hx
      dsimp only [F]
      rw [image_eq_zero_of_notMem_tsupport hx,fderiv_of_notMem_tsupport ℝ hx]
      simp)
    simpa only [Measure.restrict_univ] using hh
  have hGm : StronglyMeasurable G := by
    have hm : StronglyMeasurable (fun x : Space n => if 0 < w x then fderiv ℝ w x else 0) :=
      StronglyMeasurable.ite (isOpen_lt continuous_const hw.continuous).measurableSet
        (hw.continuous_fderiv (by simp)).stronglyMeasurable stronglyMeasurable_const
    exact (hφ.continuous.stronglyMeasurable.smul hm).add
      (hv.stronglyMeasurable.smul (hφ.continuous_fderiv (by simp)).stronglyMeasurable)
  have hGbound (x : Space n) : ‖G x‖^2 ≤ F x := by
    have h := dg_cutoff_linear_norm_bound (φ x) (v x) (v x) (if 0 < w x then 1 else 0)
      (fderiv ℝ w x) (fderiv ℝ φ x) ⟨hv0 x,le_rfl⟩ (by split_ifs <;> norm_num)
    simpa only [G,F,ite_smul,one_smul,zero_smul] using h
  have hGI : Integrable (fun x => ‖G x‖^2) volume := by
    apply hFI.mono' (hGm.norm.pow 2).aestronglyMeasurable
    exact ae_of_all _ fun x => by
      change ‖‖G x‖^2‖ ≤ F x
      rw [Real.norm_of_nonneg (sq_nonneg _)]
      exact hGbound x
  have hzbound (j : ℕ) (x : Space n) : |z j x| ≤ |v x*φ x| := by
    dsimp only [z]
    rw [abs_mul,abs_mul,abs_of_nonneg (dgSmoothPos_bounds (hε j) (w x)).1,abs_of_nonneg (hv0 x)]
    exact mul_le_mul_of_nonneg_right (dgSmoothPos_bounds (hε j) (w x)).2 (abs_nonneg _)
  have hzlim (x : Space n) : Tendsto (fun j => z j x) atTop (𝓝 (v x*φ x)) :=
    (dgSmoothPos_tendsto hε hεlim (w x)).mul tendsto_const_nhds
  have hdlim (x : Space n) : Tendsto (fun j => fderiv ℝ (z j) x) atTop (𝓝 (G x)) := by
    have hβ := dgSmoothPos_tendsto hε hεlim (w x)
    have hθ := dgSmoothStep_tendsto hε hεlim (w x)
    have hh : Tendsto (fun j => φ x • (dgSmoothStep (ε j) (w x) • fderiv ℝ w x)+
        dgSmoothPos (ε j) (w x) • fderiv ℝ φ x) atTop
        (𝓝 (φ x • ((if 0 < w x then (1:ℝ) else 0) • fderiv ℝ w x)+v x • fderiv ℝ φ x)) :=
      (tendsto_const_nhds.smul (hθ.smul tendsto_const_nhds)).add (hβ.smul tendsto_const_nhds)
    simp only [ite_smul,one_smul,zero_smul] at hh
    simpa only [hdz,G] using hh
  have hA : Tendsto (fun j => ∫ x, |z j x|^q) atTop (𝓝 (∫ x, |v x*φ x|^q)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => |v x*φ x|^q)
      (fun j => ((Real.continuous_rpow_const hq.le).comp (hz j).continuous.abs).aestronglyMeasurable) hAI
    · intro j
      exact ae_of_all _ fun x => by
        change ‖|z j x|^q‖ ≤ |v x*φ x|^q
        rw [Real.norm_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _)]
        exact Real.rpow_le_rpow (abs_nonneg _) (hzbound j x) hq.le
    · exact ae_of_all _ fun x => (Real.continuous_rpow_const hq.le).continuousAt.tendsto.comp (hzlim x).abs
  have hB : Tendsto (fun j => ∫ x, (z j x)^2) atTop (𝓝 (∫ x, (v x*φ x)^2)) := by
    apply tendsto_integral_of_dominated_convergence (fun x => (v x*φ x)^2)
      (fun j => ((hz j).continuous.pow 2).aestronglyMeasurable) hBI
    · intro j
      exact ae_of_all _ fun x => by
        change ‖(z j x)^2‖ ≤ (v x*φ x)^2
        rw [Real.norm_of_nonneg (sq_nonneg _)]
        have h := (sq_le_sq₀ (abs_nonneg _) (abs_nonneg _)).mpr (hzbound j x)
        simpa only [sq_abs] using h
    · exact ae_of_all _ fun x => (hzlim x).pow 2
  have hE : Tendsto (fun j => ∫ x, ‖fderiv ℝ (z j) x‖^2) atTop (𝓝 (∫ x, ‖G x‖^2)) := by
    apply tendsto_integral_of_dominated_convergence F
      (fun j => (((hz j).continuous_fderiv (by simp)).norm.pow 2).aestronglyMeasurable) hFI
    · intro j
      exact ae_of_all _ fun x => by
        change ‖‖fderiv ℝ (z j) x‖^2‖ ≤ F x
        rw [Real.norm_of_nonneg (sq_nonneg _),hdz]
        exact dg_cutoff_linear_norm_bound (φ x) (v x) (dgSmoothPos (ε j) (w x)) (dgSmoothStep (ε j) (w x))
          (fderiv ℝ w x) (fderiv ℝ φ x) (dgSmoothPos_bounds (hε j) (w x)) (dgSmoothStep_bounds _ _)
    · exact ae_of_all _ fun x => (hdlim x).norm.pow 2
  have hPow := (Real.continuous_rpow_const (by positivity : 0 ≤ (n:ℝ)⁻¹)).continuousAt.tendsto.comp hB
  have hRight : Tendsto (fun j => S*(∫ x, (z j x)^2)^((n:ℝ)⁻¹)*(∫ x, ‖fderiv ℝ (z j) x‖^2))
      atTop (𝓝 (S*(∫ x, (v x*φ x)^2)^((n:ℝ)⁻¹)*(∫ x, ‖G x‖^2))) :=
    (tendsto_const_nhds.mul hPow).mul hE
  have hFinal : (∫ x, |v x*φ x|^q) ≤
      S*(∫ x, (v x*φ x)^2)^((n:ℝ)⁻¹)*(∫ x, ‖G x‖^2) := by
    apply le_of_tendsto_of_tendsto hA hRight
    exact Eventually.of_forall (fun j => by
      have hh := hGN (z j) ((hz j).of_le (by simp)) (hcz j)
      simpa only [q,← dg_fderiv_norm_sq] using hh)
  exact ⟨hAI,hBI,hGI,hFinal⟩


/-- The actual positive-part product gradient in coordinate form. -/
theorem dg_positive_cutoff_dual_sq {n : ℕ} (w φ : Space n → ℝ) (x : Space n) :
    ‖φ x • (if 0 < w x then fderiv ℝ w x else 0)+dgPositivePart (w x) • fderiv ℝ φ x‖^2 =
      dgGradientSq (fun i => φ x*(if 0 < w x then d w x i else 0)+dgPositivePart (w x)*d φ x i) := by
  rw [(complexVector_realOrthonormalBasis n).norm_dual]
  apply Finset.sum_congr rfl
  intro i _
  rw [complexVector_realOrthonormalBasis_apply]
  dsimp only [dgGradientSq,d]
  split_ifs <;> simp only [add_apply,smul_apply,smul_eq_mul,zero_apply,mul_zero]

/-- Localization of the genuine truncation inequality to an arbitrary open
region, with a smooth cutoff compactly supported there. -/
theorem dg_spatial_positivePart_sobolev {n : ℕ} (hn : 0 < n) :
    ∃ S : ℝ, 0 < S ∧ ∀ (O : Set (Space n)), IsOpen O → ∀ w φ : Space n → ℝ,
      ContDiffOn ℝ ∞ w O → ContDiff ℝ ∞ φ → HasCompactSupport φ → tsupport φ ⊆ O →
      let v : Space n → ℝ := fun x => dgPositivePart (w x)
      let G : Space n → Space n →L[ℝ] ℝ := fun x =>
        φ x • (if 0 < w x then fderiv ℝ w x else 0)+v x • fderiv ℝ φ x
      Integrable (fun x => |v x*φ x|^((2:ℝ)+2/n)) (volume.restrict O) ∧
      Integrable (fun x => (v x*φ x)^2) (volume.restrict O) ∧
      Integrable (fun x => ‖G x‖^2) (volume.restrict O) ∧
      (∫ x in O, |v x*φ x|^((2:ℝ)+2/n)) ≤
        S*(∫ x in O, (v x*φ x)^2)^((n:ℝ)⁻¹)*(∫ x in O, ‖G x‖^2) := by
  obtain ⟨S,hS,hGN⟩ := dg_spatial_positivePart_sobolev_global hn
  refine ⟨S,hS,?_⟩
  intro O hO w φ hw hφ hcφ hφO
  obtain ⟨we,hwe,hcwe,hnear⟩ := dg_smooth_compact_extension hO hcφ hφO hw
  let v : Space n → ℝ := fun x => dgPositivePart (w x)
  let ve : Space n → ℝ := fun x => dgPositivePart (we x)
  let G : Space n → Space n →L[ℝ] ℝ := fun x =>
    φ x • (if 0 < w x then fderiv ℝ w x else 0)+v x • fderiv ℝ φ x
  let Ge : Space n → Space n →L[ℝ] ℝ := fun x =>
    φ x • (if 0 < we x then fderiv ℝ we x else 0)+ve x • fderiv ℝ φ x
  have hv (x : Space n) : ve x*φ x = v x*φ x := by
    by_cases hx : x ∈ tsupport φ
    · dsimp only [ve,v]; rw [(hnear x hx).eq_of_nhds]
    · rw [image_eq_zero_of_notMem_tsupport hx]; simp
  have hG (x : Space n) : Ge x = G x := by
    by_cases hx : x ∈ tsupport φ
    · dsimp only [Ge,G,ve,v]
      rw [(hnear x hx).eq_of_nhds,(hnear x hx).fderiv_eq (𝕜 := ℝ)]
    · dsimp only [Ge,G]
      rw [image_eq_zero_of_notMem_tsupport hx,fderiv_of_notMem_tsupport ℝ hx]
      simp
  obtain ⟨hAI,hBI,hGI,hI⟩ := hGN we φ hwe hφ hcφ
  change Integrable (fun x => |ve x*φ x|^((2:ℝ)+2/n)) volume at hAI
  change Integrable (fun x => (ve x*φ x)^2) volume at hBI
  change Integrable (fun x => ‖Ge x‖^2) volume at hGI
  change (∫ x, |ve x*φ x|^((2:ℝ)+2/n)) ≤
    S*(∫ x, (ve x*φ x)^2)^((n:ℝ)⁻¹)*(∫ x, ‖Ge x‖^2) at hI
  simp_rw [hv,hG] at hAI hBI hGI hI
  have hz (x : Space n) (hx : x ∉ O) : φ x = 0 ∧ fderiv ℝ φ x = 0 := by
    have hxφ : x ∉ tsupport φ := fun h => hx (hφO h)
    exact ⟨image_eq_zero_of_notMem_tsupport hxφ,fderiv_of_notMem_tsupport ℝ hxφ⟩
  have hAeq : (∫ x in O, |v x*φ x|^((2:ℝ)+2/n)) = ∫ x, |v x*φ x|^((2:ℝ)+2/n) := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [(hz x hx).1,mul_zero,abs_zero,Real.zero_rpow (by positivity : (2:ℝ)+2/n ≠ 0)]
  have hBeq : (∫ x in O, (v x*φ x)^2) = ∫ x, (v x*φ x)^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    rw [(hz x hx).1,mul_zero]; norm_num
  have hGeq : (∫ x in O, ‖G x‖^2) = ∫ x, ‖G x‖^2 := by
    apply setIntegral_eq_integral_of_forall_compl_eq_zero
    intro x hx
    dsimp only [G]
    rw [(hz x hx).1,(hz x hx).2]
    simp
  refine ⟨hAI.integrableOn,hBI.integrableOn,hGI.integrableOn,?_⟩
  rw [hAeq,hBeq,hGeq]
  exact hI


/-- The first-gradient parabolic Sobolev inequality for the actual signed
truncation and its actual cutoff gradient. The number M is an upper bound for
every genuine time-slice energy, exactly as supplied by Caccioppoli. -/
theorem dg_parabolic_sobolev {n : ℕ} (hn : 0 < n) :
    ∃ S : ℝ, 0 < S ∧ ∀ (O : Set (Space n)), IsOpen O → ∀ a b : ℝ, a < b →
      ∀ u ζ : Point n → ℝ, ContDiffOn ℝ ∞ u (O ×ˢ Ioo a b) → DGSpatialCutoff O a b ζ →
      ∀ σ k M : ℝ, 0 ≤ M →
      Integrable (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) (productVolume O (Ioo a b)) →
      (∀ t ∈ Ioo a b, dgSliceEnergy O (dgTruncation σ k u) ζ t ≤ M) →
      Integrable (fun z => |dgTruncation σ k u z*ζ z|^((2:ℝ)+2/n)) (productVolume O (Ioo a b)) ∧
      dgCylinderIntegral O a b (fun z => |dgTruncation σ k u z*ζ z|^((2:ℝ)+2/n)) ≤
        S*M^((n:ℝ)⁻¹)*dgCylinderIntegral O a b
          (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) := by
  obtain ⟨S,hS,hGN⟩ := dg_spatial_positivePart_sobolev hn
  refine ⟨S,hS,?_⟩
  intro O hO a b hab u ζ hu hζ σ k M hM hEI hSliceM
  obtain ⟨hζs,_hζr,K,hK,hKO,hzero⟩ := hζ
  let μ : Measure (Point n) := productVolume O (Ioo a b)
  let μx : Measure (Space n) := volume.restrict O
  let ν : Measure ℝ := volume.restrict (Ioo a b)
  let v : Point n → ℝ := dgTruncation σ k u
  let E : Point n → ℝ := fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)
  let q : ℝ := 2+2/(n:ℝ)
  let Z : Point n → ℝ := fun z => |v z*ζ z|^q
  let A : ℝ := S*M^((n:ℝ)⁻¹)
  have hA : 0 ≤ A := mul_nonneg hS.le (Real.rpow_nonneg hM _)
  have hq : 0 < q := by dsimp [q]; positivity
  have hU : IsOpen (O ×ˢ Ioo a b) := hO.prod isOpen_Ioo
  have hEnonneg (z : Point n) : 0 ≤ E z := dgGradientSq_nonneg _
  have hZnonneg (z : Point n) : 0 ≤ Z z := Real.rpow_nonneg (abs_nonneg _) _
  have hSlice (t : ℝ) (ht : t ∈ Ioo a b) :
      Integrable (fun x => Z (x,t)) μx ∧
      (∫ x, Z (x,t) ∂μx) ≤ A*(∫ x, E (x,t) ∂μx) := by
    let w : Space n → ℝ := fun x => σ*u (x,t)-k
    let φ : Space n → ℝ := fun x => ζ (x,t)
    have hw : ContDiffOn ℝ ∞ w O :=
      (contDiffOn_const.mul (hu.comp (contDiff_id.prodMk contDiff_const).contDiffOn
        (fun x hx => ⟨hx,ht⟩))).sub contDiffOn_const
    have hφ : ContDiff ℝ ∞ φ := hζs.comp (contDiff_id.prodMk contDiff_const)
    have hsupp : tsupport φ ⊆ K := by
      apply hK.isClosed.closure_subset_iff.mpr
      intro x hx
      by_contra hxK
      exact hx (hzero (x,t) (Ioo_subset_Icc_self ht) hxK)
    have hcφ : HasCompactSupport φ := hK.of_isClosed_subset (isClosed_tsupport _) hsupp
    obtain ⟨hPI,hBI,hGI,hP⟩ := hGN O hO w φ hw hφ hcφ (hsupp.trans hKO)
    have hgrad (x : Space n) (hx : x ∈ O) :
        ‖φ x • (if 0 < w x then fderiv ℝ w x else 0)+dgPositivePart (w x) • fderiv ℝ φ x‖^2 = E (x,t) := by
      rw [dg_positive_cutoff_dual_sq]
      unfold dgGradientSq
      apply Finset.sum_congr rfl
      intro i _
      have hd : d w x i = σ*dgGradient u (x,t) i := by
        change dgGradient (fun p => σ*u p-k) (x,t) i = σ*dgGradient u (x,t) i
        exact dgGradient_affine ((hu.contDiffAt (hU.mem_nhds ⟨hx,ht⟩)).differentiableAt (by simp)) σ k i
      have he : (0 < w x) ↔ k < σ*u (x,t) := by dsimp only [w]; exact sub_pos
      change (φ x*(if 0 < w x then d w x i else 0)+dgPositivePart (w x)*d φ x i)^2 =
        (dgTruncationCutoffGradient σ k u ζ (x,t) i)^2
      simp only [hd,he]
      rfl
    have hGeq : (∫ x in O,
        ‖φ x • (if 0 < w x then fderiv ℝ w x else 0)+dgPositivePart (w x) • fderiv ℝ φ x‖^2) =
        ∫ x, E (x,t) ∂μx := setIntegral_congr_fun hO.measurableSet hgrad
    have hBeq : (∫ x in O, (dgPositivePart (w x)*φ x)^2) =
        dgSliceEnergy O (dgTruncation σ k u) ζ t := by
      simp only [dgSliceEnergy,dgTruncation,w,φ,mul_pow]
    rw [hGeq,hBeq] at hP
    change Integrable (fun x => Z (x,t)) μx at hPI
    change (∫ x, Z (x,t) ∂μx) ≤ S*(dgSliceEnergy O (dgTruncation σ k u) ζ t)^((n:ℝ)⁻¹)*
      (∫ x, E (x,t) ∂μx) at hP
    refine ⟨hPI,hP.trans ?_⟩
    have hB0 : 0 ≤ dgSliceEnergy O (dgTruncation σ k u) ζ t := by
      exact integral_nonneg fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _)
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hB0 (hSliceM t ht) (by positivity)) hS.le)
      (integral_nonneg fun x => hEnonneg (x,t))
  have hVC : ContinuousOn v (O ×ˢ Ioo a b) :=
    dgPositivePart_lipschitz.continuous.comp_continuousOn
      ((continuousOn_const.mul hu.continuousOn).sub continuousOn_const)
  have hZC : ContinuousOn Z (O ×ˢ Ioo a b) :=
    (Real.continuous_rpow_const hq.le).comp_continuousOn ((hVC.mul hζs.continuous.continuousOn).abs)
  let F : ℝ → Space n → ℝ := fun t x => Z (x,t)
  have hFm : AEStronglyMeasurable (Function.uncurry F) (ν.prod μx) := by
    have hc : ContinuousOn (Function.uncurry F) (Ioo a b ×ˢ O) :=
      hZC.comp continuous_swap.continuousOn (fun p hp => ⟨hp.2,hp.1⟩)
    dsimp only [ν,μx]
    rw [Measure.prod_restrict]
    exact hc.aestronglyMeasurable (measurableSet_Ioo.prod hO.measurableSet)
  have hEswap : Integrable (fun p : ℝ × Space n => E (p.2,p.1)) (ν.prod μx) := by
    apply hEI.swap.congr
    exact ae_of_all _ fun p => by cases p; rfl
  have hEtI : Integrable (fun t => ∫ x, E (x,t) ∂μx) ν := hEswap.integral_prod_left
  have hFnI : Integrable (fun t => ∫ x, ‖F t x‖ ∂μx) ν := by
    apply (hEtI.const_mul A).mono' hFm.norm.integral_prod_right'
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    have he : (fun x => ‖F t x‖) = fun x => F t x :=
      funext fun x => Real.norm_of_nonneg (hZnonneg (x,t))
    change ‖∫ x, ‖F t x‖ ∂μx‖ ≤ A*(∫ x, E (x,t) ∂μx)
    rw [he,Real.norm_of_nonneg (integral_nonneg fun x => hZnonneg (x,t))]
    exact (hSlice t ht).2
  have hProdF : Integrable (Function.uncurry F) (ν.prod μx) := by
    apply (integrable_prod_iff hFm).mpr
    refine ⟨?_,hFnI⟩
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
    exact (hSlice t ht).1
  have hZI : Integrable Z μ := by
    apply hProdF.swap.congr
    exact ae_of_all _ fun p => by cases p; rfl
  refine ⟨hZI,?_⟩
  change (∫ z, Z z ∂μ) ≤ A*(∫ z, E z ∂μ)
  rw [show μ = μx.prod ν from rfl,integral_prod_symm _ hZI]
  calc
    _ ≤ ∫ t, A*(∫ x, E (x,t) ∂μx) ∂ν := by
      apply integral_mono_ae hProdF.integral_prod_left (hEtI.const_mul A)
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with t ht
      exact (hSlice t ht).2
    _ = A*(∫ t, ∫ x, E (x,t) ∂μx ∂ν) := integral_const_mul _ _
    _ = _ := by rw [← integral_prod_symm _ hEI]


/-- The d=2 parabolic branch has exponent four and exactly one slice-energy factor. -/
theorem dg_parabolic_sobolev_dimension_two :
    ∃ S : ℝ, 0 < S ∧ ∀ (O : Set (Space 1)), IsOpen O → ∀ a b : ℝ, a < b →
      ∀ u ζ : Point 1 → ℝ, ContDiffOn ℝ ∞ u (O ×ˢ Ioo a b) → DGSpatialCutoff O a b ζ →
      ∀ σ k M : ℝ, 0 ≤ M →
      Integrable (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) (productVolume O (Ioo a b)) →
      (∀ t ∈ Ioo a b, dgSliceEnergy O (dgTruncation σ k u) ζ t ≤ M) →
      Integrable (fun z => |dgTruncation σ k u z*ζ z|^4) (productVolume O (Ioo a b)) ∧
      dgCylinderIntegral O a b (fun z => |dgTruncation σ k u z*ζ z|^4) ≤
        S*M*dgCylinderIntegral O a b
          (fun z => dgGradientSq (dgTruncationCutoffGradient σ k u ζ z)) := by
  simpa only [Nat.cast_one,div_one,show (2:ℝ)+2 = 4 by norm_num,
    Real.rpow_ofNat,inv_one,Real.rpow_one] using dg_parabolic_sobolev (n := 1) (by norm_num)


/-- L1 two-point Poincare on an actual Euclidean ball. The coefficient is
2^(d+1) R |B|, d=2n, and every product integral is proved integrable first. -/
theorem dg_ball_poincare_two_point {n : ℕ} (c : Space n) {R : ℝ} (hR : 0 < R)
    {g : Space n → ℝ} (hg : ContDiff ℝ 1 g) :
    let B := Metric.ball c R
    let μB : Measure (Space n) := volume.restrict B
    Integrable (fun p : Space n × Space n => |g p.1-g p.2|) (μB.prod μB) ∧
    (∫ p : Space n × Space n, |g p.1-g p.2| ∂μB.prod μB) ≤
      (2:ℝ)^(2*n+1)*R*volume.real B*(∫ x in B, ‖fderiv ℝ g x‖) := by
  let B := Metric.ball c R
  let μB : Measure (Space n) := volume.restrict B
  let ν : Measure ℝ := volume.restrict (Ioc (0:ℝ) 1)
  let : IsFiniteMeasure μB := ⟨by
    simpa only [μB,Measure.restrict_apply_univ] using (measure_ball_lt_top : volume (Metric.ball c R) < ⊤)⟩
  let : IsFiniteMeasure ν := ⟨by simp [ν]⟩
  let F : ℝ → Space n × Space n → ℝ := fun t p => ‖fderiv ℝ g (p.1+t • (p.2-p.1))‖
  have hDC : Continuous (fun x : Space n => ‖fderiv ℝ g x‖) := (hg.continuous_fderiv (by simp)).norm
  have hDI : IntegrableOn (fun x => ‖fderiv ℝ g x‖) B volume :=
    (hDC.continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set Metric.ball_subset_closedBall
  obtain ⟨M,hM⟩ := (isCompact_closedBall c R).bddAbove_image hDC.continuousOn
  have hGradBound (x : Space n) (hx : x ∈ Metric.closedBall c R) : ‖fderiv ℝ g x‖ ≤ max 1 M :=
    (hM ⟨x,hx,rfl⟩).trans (le_max_right _ _)
  have hPairMeasure : μB.prod μB = ((volume : Measure (Space n)).prod volume).restrict (B ×ˢ B) := by
    simp only [μB,Measure.prod_restrict]
  have hTripleMeasure : ν.prod (μB.prod μB) =
      ((volume : Measure ℝ).prod ((volume : Measure (Space n)).prod volume)).restrict
        (Ioc (0:ℝ) 1 ×ˢ (B ×ˢ B)) := by
    simp only [ν,μB,Measure.prod_restrict]
  have hFC : Continuous (Function.uncurry F) := hDC.comp (by fun_prop)
  have hFI : Integrable (Function.uncurry F) (ν.prod (μB.prod μB)) := by
    apply (integrable_const (max 1 M)).mono' hFC.aestronglyMeasurable
    rw [hTripleMeasure]
    filter_upwards [ae_restrict_mem (measurableSet_Ioc.prod (measurableSet_ball.prod measurableSet_ball))] with p hp
    change ‖F p.1 p.2‖ ≤ max 1 M
    rw [Real.norm_of_nonneg (norm_nonneg _)]
    exact hGradBound _ (Metric.ball_subset_closedBall ((convex_ball c R).add_smul_sub_mem hp.2.1 hp.2.2
      ⟨hp.1.1.le,hp.1.2⟩))
  have hSliceBound : ∀ᵐ t ∂ν, (∫ p, F t p ∂μB.prod μB) ≤
      (2:ℝ)^(2*n)*volume.real B*(∫ x in B, ‖fderiv ℝ g x‖) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioc,hFI.prod_right_ae] with t ht hFt
    change Integrable (F t) (μB.prod μB) at hFt
    by_cases hhalf : t ≤ 1/2
    · rw [integral_prod_symm _ hFt]
      calc
        _ ≤ ∫ _y, (2:ℝ)^(2*n)*(∫ x in B, ‖fderiv ℝ g x‖) ∂μB := by
          apply integral_mono_ae hFt.integral_prod_right (integrable_const _)
          filter_upwards [ae_restrict_mem measurableSet_ball] with y hy
          have hh := dg_segment_ball_integral_le_half hy
            (show 1-t ∈ Icc (1/2:ℝ) 1 by constructor <;> linarith [ht.1]) hDI (fun x _ => norm_nonneg _)
          have he (x y : Space n) : x+t • (y-x) = y+(1-t) • (x-y) := by module
          simpa only [F,he] using hh
        _ = _ := by simp only [integral_const,smul_eq_mul,μB,Measure.real,Measure.restrict_apply_univ]; ring
    · rw [integral_prod _ hFt]
      calc
        _ ≤ ∫ _x, (2:ℝ)^(2*n)*(∫ y in B, ‖fderiv ℝ g y‖) ∂μB := by
          apply integral_mono_ae hFt.integral_prod_left (integrable_const _)
          filter_upwards [ae_restrict_mem measurableSet_ball] with x hx
          have hh := dg_segment_ball_integral_le_half hx
            (show t ∈ Icc (1/2:ℝ) 1 by exact ⟨(lt_of_not_ge hhalf).le,ht.2⟩) hDI (fun y _ => norm_nonneg _)
          simpa only [F] using hh
        _ = _ := by simp only [integral_const,smul_eq_mul,μB,Measure.real,Measure.restrict_apply_univ]; ring
  have hTripleBound : (∫ t, ∫ p, F t p ∂μB.prod μB ∂ν) ≤
      (2:ℝ)^(2*n)*volume.real B*(∫ x in B, ‖fderiv ℝ g x‖) := by
    calc
      _ ≤ ∫ _t, (2:ℝ)^(2*n)*volume.real B*(∫ x in B, ‖fderiv ℝ g x‖) ∂ν :=
        integral_mono_ae hFI.integral_prod_left (integrable_const _) hSliceBound
      _ = _ := by simp [ν,Measure.real]
  let H : Space n × Space n → ℝ := fun p => ∫ t, F t p ∂ν
  have hHI : Integrable H (μB.prod μB) := hFI.integral_prod_right
  have hPoint (x y : Space n) (hx : x ∈ B) (hy : y ∈ B) : |g x-g y| ≤ (2*R)*H (x,y) := by
    have hh := dg_segment_norm_le isOpen_univ convex_univ hg.contDiffOn (mem_univ x) (mem_univ y)
    rw [intervalIntegral.integral_of_le zero_le_one] at hh
    change |g y-g x| ≤ ∫ t, F t (x,y)*‖y-x‖ ∂ν at hh
    rw [integral_mul_const] at hh
    have hdist : ‖y-x‖ ≤ 2*R := by
      have hx' : ‖x-c‖ < R := by simpa only [B,Metric.mem_ball,dist_eq_norm] using hx
      have hy' : ‖y-c‖ < R := by simpa only [B,Metric.mem_ball,dist_eq_norm] using hy
      calc
        _ = ‖(y-c)-(x-c)‖ := by congr 1; abel
        _ ≤ ‖y-c‖+‖x-c‖ := norm_sub_le _ _
        _ ≤ _ := by linarith
    rw [abs_sub_comm]
    have hpos : 0 ≤ ∫ t, F t (x,y) ∂ν := integral_nonneg fun t => norm_nonneg _
    exact hh.trans (calc
      _ ≤ (∫ t, F t (x,y) ∂ν)*(2*R) := mul_le_mul_of_nonneg_left hdist hpos
      _ = _ := by dsimp only [H]; ring)
  have hDiffC : Continuous (fun p : Space n × Space n => |g p.1-g p.2|) :=
    ((hg.continuous.comp continuous_fst).sub (hg.continuous.comp continuous_snd)).abs
  have hDiffI : Integrable (fun p : Space n × Space n => |g p.1-g p.2|) (μB.prod μB) := by
    apply (hHI.const_mul (2*R)).mono' hDiffC.aestronglyMeasurable
    rw [hPairMeasure]
    filter_upwards [ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)] with p hp
    change ‖|g p.1-g p.2|‖ ≤ (2*R)*H p
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    exact hPoint p.1 p.2 hp.1 hp.2
  refine ⟨hDiffI,?_⟩
  calc
    _ ≤ ∫ p, (2*R)*H p ∂μB.prod μB := by
      apply integral_mono_ae hDiffI (hHI.const_mul (2*R))
      rw [hPairMeasure]
      filter_upwards [ae_restrict_mem (measurableSet_ball.prod measurableSet_ball)] with p hp
      exact hPoint p.1 p.2 hp.1 hp.2
    _ = (2*R)*(∫ p, H p ∂μB.prod μB) := integral_const_mul _ _
    _ = (2*R)*(∫ t, ∫ p, F t p ∂μB.prod μB ∂ν) := by
      congr 1
      exact (integral_integral_swap hFI).symm
    _ ≤ (2*R)*((2:ℝ)^(2*n)*volume.real B*(∫ x in B, ‖fderiv ℝ g x‖)) :=
      mul_le_mul_of_nonneg_left hTripleBound (by positivity)
    _ = _ := by rw [pow_succ]; ring


/-- Actual clipping between two levels, written as a difference of positive parts. -/
def dgClamp (a b r : ℝ) : ℝ := dgPositivePart (r-a)-dgPositivePart (r-b)

theorem dgClamp_zero {a b r : ℝ} (hab : a ≤ b) (hr : r ≤ a) : dgClamp a b r = 0 := by
  rw [dgClamp,dgPositivePart_of_nonpos (by linarith : r-a ≤ 0),
    dgPositivePart_of_nonpos (by linarith : r-b ≤ 0),sub_self]

theorem dgClamp_gap {a b r : ℝ} (hab : a ≤ b) (hr : b ≤ r) : dgClamp a b r = b-a := by
  rw [dgClamp,dgPositivePart_of_nonneg (by linarith : 0 ≤ r-a),
    dgPositivePart_of_nonneg (by linarith : 0 ≤ r-b)]
  ring

theorem dgClamp_middle {a b r : ℝ} (hr : a < r ∧ r < b) : dgClamp a b r = r-a := by
  rw [dgClamp,dgPositivePart_of_nonneg (by linarith [hr.1] : 0 ≤ r-a),
    dgPositivePart_of_nonpos (by linarith [hr.2] : r-b ≤ 0),sub_zero]

theorem dgClamp_bounds {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    0 ≤ dgClamp a b r ∧ dgClamp a b r ≤ b-a := by
  by_cases hr : r ≤ a
  · rw [dgClamp_zero hab hr]; exact ⟨le_rfl,sub_nonneg.mpr hab⟩
  by_cases hrb : b ≤ r
  · rw [dgClamp_gap hab hrb]; exact ⟨sub_nonneg.mpr hab,le_rfl⟩
  rw [dgClamp_middle ⟨lt_of_not_ge hr,lt_of_not_ge hrb⟩]
  constructor <;> linarith

theorem dgClamp_continuous (a b : ℝ) : Continuous (dgClamp a b) :=
  (dgPositivePart_lipschitz.continuous.comp (continuous_id.sub continuous_const)).sub
    (dgPositivePart_lipschitz.continuous.comp (continuous_id.sub continuous_const))

/-- The shifted upper smoothing makes the derivative vanish at BOTH levels. -/
def dgSmoothClamp (ε a b r : ℝ) : ℝ :=
  dgSmoothPos ε (r-a)-dgSmoothPos ε (r-b+ε)

theorem dgSmoothClamp_contDiff (ε a b : ℝ) : ContDiff ℝ ∞ (dgSmoothClamp ε a b) :=
  ((dgSmoothPos_contDiff ε).comp (contDiff_id.sub contDiff_const)).sub
    ((dgSmoothPos_contDiff ε).comp ((contDiff_id.sub contDiff_const).add contDiff_const))

theorem dgSmoothClamp_hasDerivAt (ε a b r : ℝ) :
    HasDerivAt (dgSmoothClamp ε a b)
      (dgSmoothStep ε (r-a)-dgSmoothStep ε (r-b+ε)) r := by
  have h1 := (dgSmoothPos_hasDerivAt ε (r-a)).comp r ((hasDerivAt_id r).sub_const a)
  have h2 := (dgSmoothPos_hasDerivAt ε (r-b+ε)).comp r (((hasDerivAt_id r).sub_const b).add_const ε)
  convert h1.sub h2 using 1 <;> simp only [Function.comp_def,Pi.sub_def,id_eq,mul_one]
  funext x
  rfl

theorem dgSmoothClamp_step_bounds {ε a b : ℝ} (hε : 0 < ε) (hgap : ε ≤ b-a) (r : ℝ) :
    0 ≤ dgSmoothStep ε (r-a)-dgSmoothStep ε (r-b+ε) ∧
      dgSmoothStep ε (r-a)-dgSmoothStep ε (r-b+ε) ≤ 1 := by
  have hm : dgSmoothStep ε (r-b+ε) ≤ dgSmoothStep ε (r-a) := by
    apply Real.smoothTransition.monotone
    exact (div_le_div_iff_of_pos_right hε).mpr (by linarith)
  have h1 := dgSmoothStep_bounds ε (r-a)
  have h2 := dgSmoothStep_bounds ε (r-b+ε)
  constructor <;> linarith

theorem dgSmoothClamp_step_zero {ε a b r : ℝ} (hε : 0 < ε) (hgap : ε ≤ b-a)
    (hr : r ≤ a ∨ b ≤ r) : dgSmoothStep ε (r-a)-dgSmoothStep ε (r-b+ε) = 0 := by
  rcases hr with hr | hr
  · rw [dgSmoothStep_zero hε (by linarith : r-a ≤ 0),
      dgSmoothStep_zero hε (by linarith : r-b+ε ≤ 0),sub_self]
  · rw [dgSmoothStep_one hε (by linarith : ε ≤ r-a),
      dgSmoothStep_one hε (by linarith : ε ≤ r-b+ε),sub_self]

theorem dgSmoothPos_shift_bounds {ε : ℝ} (hε : 0 < ε) (r : ℝ) :
    dgPositivePart r-ε ≤ dgSmoothPos ε (r+ε) ∧
      dgSmoothPos ε (r+ε) ≤ dgPositivePart r+ε := by
  have hm : dgPositivePart r ≤ dgPositivePart (r+ε) :=
    max_le_max le_rfl (le_add_of_nonneg_right hε.le)
  have hi : dgPositivePart (r+ε) ≤ dgPositivePart r+ε := by
    unfold dgPositivePart
    apply max_le
    · linarith [le_max_left (0:ℝ) r]
    · linarith [le_max_right (0:ℝ) r]
  have hb := dgSmoothPos_bounds hε (r+ε)
  have he := dgSmoothPos_error hε (r+ε)
  constructor <;> linarith

theorem dgSmoothClamp_error {ε : ℝ} (hε : 0 < ε) (a b r : ℝ) :
    |dgSmoothClamp ε a b r-dgClamp a b r| ≤ 2*ε := by
  have hb := dgSmoothPos_bounds hε (r-a)
  have he := dgSmoothPos_error hε (r-a)
  have hs := dgSmoothPos_shift_bounds hε (r-b)
  unfold dgSmoothClamp dgClamp
  apply abs_le.mpr
  constructor <;> linarith

theorem dgSmoothClamp_abs_bound {ε a b : ℝ} (hε : 0 < ε) (hgap : ε ≤ b-a) (r : ℝ) :
    |dgSmoothClamp ε a b r| ≤ 3*(b-a) := by
  have hab : a ≤ b := by linarith
  have hb := dgClamp_bounds hab r
  have he := dgSmoothClamp_error hε a b r
  have h := (abs_sub_le (dgSmoothClamp ε a b r) (dgClamp a b r) 0)
  simp only [sub_zero,abs_of_nonneg hb.1] at h
  linarith

theorem dgSmoothClamp_tendsto {ε : ℕ → ℝ} (hε : ∀ j, 0 < ε j)
    (hlim : Tendsto ε atTop (𝓝 0)) (a b r : ℝ) :
    Tendsto (fun j => dgSmoothClamp (ε j) a b r) atTop (𝓝 (dgClamp a b r)) := by
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le
    (show Tendsto (fun j => dgClamp a b r-2*ε j) atTop (𝓝 (dgClamp a b r)) by
      simpa using tendsto_const_nhds.sub (tendsto_const_nhds.mul hlim))
    (show Tendsto (fun j => dgClamp a b r+2*ε j) atTop (𝓝 (dgClamp a b r)) by
      simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hlim))
  · intro j; have h := neg_le_of_abs_le (dgSmoothClamp_error (hε j) a b r); dsimp; linarith
  · intro j; have h := le_of_abs_le (dgSmoothClamp_error (hε j) a b r); dsimp; linarith


/-- The genuine clipped function satisfies the ball two-point bound with gradient
restricted to the STRICT intermediate band. The two level sets cause no loss. -/
theorem dg_ball_clamp_poincare_two_point {n : ℕ} (c : Space n) {R : ℝ} (hR : 0 < R)
    {g : Space n → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a < b) :
    let B := Metric.ball c R
    let μB : Measure (Space n) := volume.restrict B
    Integrable (fun p : Space n × Space n => |dgClamp a b (g p.1)-dgClamp a b (g p.2)|) (μB.prod μB) ∧
    (∫ p : Space n × Space n, |dgClamp a b (g p.1)-dgClamp a b (g p.2)| ∂μB.prod μB) ≤
      (2:ℝ)^(2*n+1)*R*volume.real B*(∫ x in B ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ g x‖) := by
  let B := Metric.ball c R
  let μB : Measure (Space n) := volume.restrict B
  let V := {x | a < g x ∧ g x < b}
  let H : Space n → ℝ := V.indicator (fun x => ‖fderiv ℝ g x‖)
  let : IsFiniteMeasure μB := ⟨by
    simpa only [μB,Measure.restrict_apply_univ] using (measure_ball_lt_top : volume (Metric.ball c R) < ⊤)⟩
  have hV : MeasurableSet V := (isOpen_lt continuous_const hg.continuous).measurableSet.inter
    (isOpen_lt hg.continuous continuous_const).measurableSet
  have hDC : Continuous (fun x : Space n => ‖fderiv ℝ g x‖) := (hg.continuous_fderiv (by simp)).norm
  have hDI : Integrable (fun x => ‖fderiv ℝ g x‖) μB :=
    (hDC.continuousOn.integrableOn_compact (isCompact_closedBall c R)).mono_set Metric.ball_subset_closedBall
  have hHI : Integrable H μB := hDI.indicator hV
  let ε : ℕ → ℝ := fun j => ((b-a)/2)*(1/((j:ℝ)+1))
  have hε (j : ℕ) : 0 < ε j := by dsimp [ε]; positivity
  have hεgap (j : ℕ) : ε j ≤ b-a := by
    have hh : 1/((j:ℝ)+1) ≤ 1 := by apply (div_le_one (by positivity)).mpr; have hh := Nat.cast_nonneg (α := ℝ) j; linarith
    dsimp [ε]
    nlinarith [mul_le_mul_of_nonneg_left hh (show 0 ≤ (b-a)/2 by linarith)]
  have hεlim : Tendsto ε atTop (𝓝 0) := by
    simpa only [mul_zero] using tendsto_const_nhds.mul
      (tendsto_one_div_add_atTop_nhds_zero_nat : Tendsto (fun j : ℕ => 1/((j:ℝ)+1)) atTop (𝓝 0))
  let z : ℕ → Space n → ℝ := fun j x => dgSmoothClamp (ε j) a b (g x)
  have hzC (j : ℕ) : ContDiff ℝ 1 (z j) :=
    ((dgSmoothClamp_contDiff (ε j) a b).of_le (by simp)).comp hg
  have hzD (j : ℕ) (x : Space n) : fderiv ℝ (z j) x =
      (dgSmoothStep (ε j) (g x-a)-dgSmoothStep (ε j) (g x-b+ε j)) • fderiv ℝ g x := by
    exact ((dgSmoothClamp_hasDerivAt (ε j) a b (g x)).comp_hasFDerivAt x
      (hg.differentiable (by simp) x).hasFDerivAt).fderiv
  have hGrad (j : ℕ) (x : Space n) : ‖fderiv ℝ (z j) x‖ ≤ H x := by
    rw [hzD,norm_smul,Real.norm_eq_abs]
    by_cases hx : x ∈ V
    · dsimp only [H]
      rw [Set.indicator_of_mem hx]
      have hh := dgSmoothClamp_step_bounds (hε j) (hεgap j) (g x)
      rw [abs_of_nonneg hh.1]
      exact (mul_le_mul_of_nonneg_right hh.2 (norm_nonneg _)).trans_eq (one_mul _)
    · have he : g x ≤ a ∨ b ≤ g x := by dsimp [V] at hx; push Not at hx; by_cases h : g x ≤ a; exact Or.inl h; exact Or.inr (hx (lt_of_not_ge h))
      dsimp only [H]
      rw [Set.indicator_of_notMem hx,dgSmoothClamp_step_zero (hε j) (hεgap j) he]
      simp
  have hBound (j : ℕ) : (∫ p : Space n × Space n, |z j p.1-z j p.2| ∂μB.prod μB) ≤
      (2:ℝ)^(2*n+1)*R*volume.real B*(∫ x in B ∩ V, ‖fderiv ℝ g x‖) := by
    have hh := (dg_ball_poincare_two_point c hR (hzC j)).2
    have hzDI : Integrable (fun x => ‖fderiv ℝ (z j) x‖) μB :=
      hHI.mono' ((hzC j).continuous_fderiv (by simp)).norm.aestronglyMeasurable (ae_of_all _ (fun x => by
        rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hGrad j x))
    have hG : (∫ x, ‖fderiv ℝ (z j) x‖ ∂μB) ≤ ∫ x, H x ∂μB :=
      integral_mono_ae hzDI hHI (ae_of_all _ (hGrad j))
    have hEq : (∫ x, H x ∂μB) = ∫ x in B ∩ V, ‖fderiv ℝ g x‖ := setIntegral_indicator hV
    rw [hEq] at hG
    exact hh.trans (mul_le_mul_of_nonneg_left hG (by positivity))
  let F : ℕ → Space n × Space n → ℝ := fun j p => |z j p.1-z j p.2|
  let f : Space n × Space n → ℝ := fun p => |dgClamp a b (g p.1)-dgClamp a b (g p.2)|
  have hFC (j : ℕ) : Continuous (F j) :=
    (((hzC j).continuous.comp continuous_fst).sub ((hzC j).continuous.comp continuous_snd)).abs
  have hfC : Continuous f :=
    ((((dgClamp_continuous a b).comp hg.continuous).comp continuous_fst).sub
      (((dgClamp_continuous a b).comp hg.continuous).comp continuous_snd)).abs
  have hDom (j : ℕ) : ∀ᵐ p ∂μB.prod μB, ‖F j p‖ ≤ 6*(b-a) := ae_of_all _ fun p => by
    change ‖|z j p.1-z j p.2|‖ ≤ _
    rw [Real.norm_of_nonneg (abs_nonneg _)]
    have h1 := dgSmoothClamp_abs_bound (hε j) (hεgap j) (g p.1)
    have h2 := dgSmoothClamp_abs_bound (hε j) (hεgap j) (g p.2)
    dsimp only [z]
    exact (abs_sub _ _).trans (by linarith)
  have hfI : Integrable f (μB.prod μB) := by
    apply (integrable_const (6*(b-a))).mono' hfC.aestronglyMeasurable
    exact ae_of_all _ fun p => by
      rw [Real.norm_of_nonneg (abs_nonneg _)]
      have h1 := dgClamp_bounds hab.le (g p.1)
      have h2 := dgClamp_bounds hab.le (g p.2)
      exact (abs_sub _ _).trans (by rw [abs_of_nonneg h1.1,abs_of_nonneg h2.1]; linarith)
  have hLim : Tendsto (fun j => ∫ p, F j p ∂μB.prod μB) atTop (𝓝 (∫ p, f p ∂μB.prod μB)) :=
    tendsto_integral_of_dominated_convergence (fun _ => 6*(b-a))
      (fun j => (hFC j).aestronglyMeasurable) (integrable_const _) hDom
      (ae_of_all _ fun p => ((dgSmoothClamp_tendsto hε hεlim a b (g p.1)).sub
        (dgSmoothClamp_tendsto hε hεlim a b (g p.2))).abs)
  exact ⟨hfI,le_of_tendsto_of_tendsto hLim tendsto_const_nhds (Eventually.of_forall hBound)⟩


/-- Relative Poincare on a ball, with the genuine strict-band gradient. -/
theorem dg_ball_relative_poincare {n : ℕ} (c : Space n) {R : ℝ} (hR : 0 < R)
    {g : Space n → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a < b) :
    (b-a)*volume.real (Metric.ball c R ∩ {x | g x ≤ a})*
      volume.real (Metric.ball c R ∩ {x | b ≤ g x}) ≤
      (2:ℝ)^(2*n+1)*R*volume.real (Metric.ball c R)*
        (∫ x in Metric.ball c R ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ g x‖) := by
  let B := Metric.ball c R
  let A := B ∩ {x | g x ≤ a}
  let C := B ∩ {x | b ≤ g x}
  let μ : Measure (Space n × Space n) := (volume : Measure (Space n)).prod volume
  let f : Space n × Space n → ℝ := fun p => |dgClamp a b (g p.1)-dgClamp a b (g p.2)|
  have hA : MeasurableSet A := measurableSet_ball.inter (isClosed_le hg.continuous continuous_const).measurableSet
  have hC : MeasurableSet C := measurableSet_ball.inter (isClosed_le continuous_const hg.continuous).measurableSet
  have hle : μ.restrict (A ×ˢ C) ≤ μ.restrict (B ×ˢ B) :=
    Measure.restrict_mono (Set.prod_mono inter_subset_left inter_subset_left) le_rfl
  have hI : Integrable f (μ.restrict (B ×ˢ B)) := by
    simpa only [μ,Measure.prod_restrict] using (dg_ball_clamp_poincare_two_point c hR hg hab).1
  have hEq : (∫ p, f p ∂μ.restrict (A ×ˢ C)) = (b-a)*volume.real A*volume.real C := by
    calc
      _ = ∫ _p, b-a ∂μ.restrict (A ×ˢ C) := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem (hA.prod hC)] with p hp
        change |dgClamp a b (g p.1)-dgClamp a b (g p.2)| = b-a
        rw [dgClamp_zero hab.le hp.1.2,dgClamp_gap hab.le hp.2.2]
        simpa only [zero_sub,abs_neg] using (abs_of_nonneg (sub_nonneg.mpr hab.le))
      _ = _ := by
        simp only [integral_const,smul_eq_mul,Measure.real,Measure.restrict_apply_univ,μ,
          Measure.prod_prod,ENNReal.toReal_mul]
        ring
  calc
    _ = ∫ p, f p ∂μ.restrict (A ×ˢ C) := hEq.symm
    _ ≤ ∫ p, f p ∂μ.restrict (B ×ˢ B) :=
      integral_mono_measure hle (ae_of_all _ fun p => abs_nonneg _) hI
    _ ≤ _ := by simpa only [μ,Measure.prod_restrict] using (dg_ball_clamp_poincare_two_point c hR hg hab).2

/-- Restricting the first variable of a two-point integral to a true zero set. -/
theorem dg_ball_zero_set_integral_le_two_point {n : ℕ} (c : Space n) {R : ℝ}
    {f : Space n → ℝ} {A : Set (Space n)} (hA : MeasurableSet A)
    (hAB : A ⊆ Metric.ball c R) (hzero : ∀ x ∈ A, f x = 0)
    (hpos : ∀ x ∈ Metric.ball c R, 0 ≤ f x)
    (hI : Integrable (fun p : Space n × Space n => |f p.1-f p.2|)
      ((volume.restrict (Metric.ball c R)).prod (volume.restrict (Metric.ball c R)))) :
    volume.real A*(∫ x in Metric.ball c R, f x) ≤
      ∫ p : Space n × Space n, |f p.1-f p.2|
        ∂(volume.restrict (Metric.ball c R)).prod (volume.restrict (Metric.ball c R)) := by
  let B := Metric.ball c R
  let μB : Measure (Space n) := volume.restrict B
  let μA : Measure (Space n) := volume.restrict A
  have hleA : μA ≤ μB := Measure.restrict_mono hAB le_rfl
  let : IsFiniteMeasure μB := ⟨by
    simpa only [μB,Measure.restrict_apply_univ] using (measure_ball_lt_top : volume (Metric.ball c R) < ⊤)⟩
  let : IsFiniteMeasure μA := ⟨lt_of_le_of_lt (hleA univ) (measure_lt_top μB univ)⟩
  have hle : μA.prod μB ≤ μB.prod μB := Measure.prod_mono hleA le_rfl
  have hsmallI := hI.mono_measure hle
  have hEq : (fun p : Space n × Space n => |f p.1-f p.2|) =ᵐ[μA.prod μB] fun p => f p.2 := by
    simp only [μA,μB,Measure.prod_restrict]
    filter_upwards [ae_restrict_mem (hA.prod measurableSet_ball)] with p hp
    rw [hzero p.1 hp.1,zero_sub,abs_neg,abs_of_nonneg (hpos p.2 hp.2)]
  have hMass : (∫ p : Space n × Space n, |f p.1-f p.2| ∂μA.prod μB) =
      volume.real A*(∫ x in B, f x) := by
    rw [integral_congr_ae hEq,integral_prod_symm _ (hsmallI.congr hEq)]
    simp only [integral_const,smul_eq_mul,μA,Measure.real,Measure.restrict_apply_univ]
    exact integral_const_mul _ _
  rw [←hMass]
  exact integral_mono_measure hle (ae_of_all _ fun p => abs_nonneg _) hI

/-- Zero-set Poincare for an actual nonnegative smooth function on the ball. -/
theorem dg_ball_zero_set_poincare {n : ℕ} (c : Space n) {R : ℝ} (hR : 0 < R)
    {g : Space n → ℝ} (hg : ContDiff ℝ 1 g) (hpos : ∀ x ∈ Metric.ball c R, 0 ≤ g x) :
    volume.real (Metric.ball c R ∩ {x | g x = 0})*(∫ x in Metric.ball c R, g x) ≤
      (2:ℝ)^(2*n+1)*R*volume.real (Metric.ball c R)*(∫ x in Metric.ball c R, ‖fderiv ℝ g x‖) := by
  have hh := dg_ball_poincare_two_point c hR hg
  exact (dg_ball_zero_set_integral_le_two_point c
    (measurableSet_ball.inter (isClosed_eq hg.continuous continuous_const).measurableSet)
    inter_subset_left (fun x hx => hx.2) hpos hh.1).trans hh.2

/-- Zero-set Poincare for a genuinely Lipschitz capped truncation, with its
strict-band actual gradient. This also applies to min(2*u_+,1) after scaling. -/
theorem dg_ball_clamp_zero_set_poincare {n : ℕ} (c : Space n) {R : ℝ} (hR : 0 < R)
    {g : Space n → ℝ} (hg : ContDiff ℝ 1 g) {a b : ℝ} (hab : a < b) :
    volume.real (Metric.ball c R ∩ {x | g x ≤ a})*(∫ x in Metric.ball c R, dgClamp a b (g x)) ≤
      (2:ℝ)^(2*n+1)*R*volume.real (Metric.ball c R)*
        (∫ x in Metric.ball c R ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ g x‖) := by
  have hh := dg_ball_clamp_poincare_two_point c hR hg hab
  exact (dg_ball_zero_set_integral_le_two_point c
    (measurableSet_ball.inter (isClosed_le hg.continuous continuous_const).measurableSet)
    inter_subset_left (fun x hx => dgClamp_zero hab.le hx.2)
    (fun x _ => (dgClamp_bounds hab.le (g x)).1) hh.1).trans hh.2


/-- The norm in the ball inequalities is precisely the actual coordinate
first-gradient length used by the De Giorgi energy, with no jet data. -/
theorem dg_fderiv_norm_eq_sqrt_gradientSq {n : ℕ} (g : Space n → ℝ) (x : Space n) :
    ‖fderiv ℝ g x‖ = Real.sqrt (dgGradientSq (fun i => d g x i)) := by
  rw [←dg_fderiv_norm_sq,Real.sqrt_sq_eq_abs,abs_of_nonneg (norm_nonneg _)]

/-- Local smooth data can be used on a compactly contained ball; the extension
is only qualitative and contributes no constant to any inequality. -/
theorem dg_ball_smooth_extension {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    (c : Space n) (R : ℝ) (hBO : Metric.closedBall c R ⊆ O)
    {g : Space n → ℝ} (hg : ContDiffOn ℝ ∞ g O) :
    ∃ w : Space n → ℝ, ContDiff ℝ ∞ w ∧
      ∀ x ∈ Metric.ball c R, w x = g x ∧ fderiv ℝ w x = fderiv ℝ g x := by
  obtain ⟨w,hw,_hc,hnear⟩ := dg_smooth_compact_extension hO (isCompact_closedBall c R) hBO hg
  exact ⟨w,hw,fun x hx => ⟨(hnear x (Metric.ball_subset_closedBall hx)).eq_of_nhds,
    (hnear x (Metric.ball_subset_closedBall hx)).fderiv_eq (𝕜 := ℝ)⟩⟩

/-- Relative Poincare for the actual locally smooth spatial slice of a field. -/
theorem dg_ball_relative_poincare_local {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    (c : Space n) {R : ℝ} (hR : 0 < R) (hBO : Metric.closedBall c R ⊆ O)
    {g : Space n → ℝ} (hg : ContDiffOn ℝ ∞ g O) {a b : ℝ} (hab : a < b) :
    (b-a)*volume.real (Metric.ball c R ∩ {x | g x ≤ a})*
      volume.real (Metric.ball c R ∩ {x | b ≤ g x}) ≤
      (2:ℝ)^(2*n+1)*R*volume.real (Metric.ball c R)*
        (∫ x in Metric.ball c R ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ g x‖) := by
  obtain ⟨w,hw,hagree⟩ := dg_ball_smooth_extension hO c R hBO hg
  have hsets (P : ℝ → Prop) : Metric.ball c R ∩ {x | P (w x)} = Metric.ball c R ∩ {x | P (g x)} := by
    ext x
    by_cases hx : x ∈ Metric.ball c R
    · simp only [mem_inter_iff,mem_ofPred_eq,hx,true_and,(hagree x hx).1]
    · simp only [mem_inter_iff,hx,false_and]
  have hh := dg_ball_relative_poincare c hR (hw.of_le (by simp)) hab
  rw [hsets (fun r => r ≤ a),hsets (fun r => b ≤ r),hsets (fun r => a < r ∧ r < b)] at hh
  have hBand : MeasurableSet (Metric.ball c R ∩ {x | a < g x ∧ g x < b}) := by
    rw [←hsets (fun r => a < r ∧ r < b)]
    exact measurableSet_ball.inter ((isOpen_lt continuous_const hw.continuous).measurableSet.inter
      (isOpen_lt hw.continuous continuous_const).measurableSet)
  have hGrad : (∫ x in Metric.ball c R ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ w x‖) =
      ∫ x in Metric.ball c R ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ g x‖ :=
    setIntegral_congr_fun hBand (fun x hx => congrArg norm (hagree x hx.1).2)
  rw [hGrad] at hh
  exact hh

/-- Local smooth nonnegative zero-set form with the same dimension constant. -/
theorem dg_ball_zero_set_poincare_local {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    (c : Space n) {R : ℝ} (hR : 0 < R) (hBO : Metric.closedBall c R ⊆ O)
    {g : Space n → ℝ} (hg : ContDiffOn ℝ ∞ g O)
    (hpos : ∀ x ∈ Metric.ball c R, 0 ≤ g x) :
    volume.real (Metric.ball c R ∩ {x | g x = 0})*(∫ x in Metric.ball c R, g x) ≤
      (2:ℝ)^(2*n+1)*R*volume.real (Metric.ball c R)*(∫ x in Metric.ball c R, ‖fderiv ℝ g x‖) := by
  obtain ⟨w,hw,hagree⟩ := dg_ball_smooth_extension hO c R hBO hg
  have hsets : Metric.ball c R ∩ {x | w x = 0} = Metric.ball c R ∩ {x | g x = 0} := by
    ext x
    by_cases hx : x ∈ Metric.ball c R
    · simp only [mem_inter_iff,mem_ofPred_eq,hx,true_and,(hagree x hx).1]
    · simp only [mem_inter_iff,hx,false_and]
  have hh := dg_ball_zero_set_poincare c hR (hw.of_le (by simp)) (fun x hx => by rw [(hagree x hx).1]; exact hpos x hx)
  rw [hsets] at hh
  have hVal : (∫ x in Metric.ball c R, w x) = ∫ x in Metric.ball c R, g x :=
    setIntegral_congr_fun measurableSet_ball (fun x hx => (hagree x hx).1)
  have hGrad : (∫ x in Metric.ball c R, ‖fderiv ℝ w x‖) = ∫ x in Metric.ball c R, ‖fderiv ℝ g x‖ :=
    setIntegral_congr_fun measurableSet_ball (fun x hx => congrArg norm (hagree x hx).2)
  simpa only [hVal,hGrad] using hh

/-- Local clipped zero-set form, suitable for the intermediate-value card. -/
theorem dg_ball_clamp_zero_set_poincare_local {n : ℕ} {O : Set (Space n)} (hO : IsOpen O)
    (c : Space n) {R : ℝ} (hR : 0 < R) (hBO : Metric.closedBall c R ⊆ O)
    {g : Space n → ℝ} (hg : ContDiffOn ℝ ∞ g O) {a b : ℝ} (hab : a < b) :
    volume.real (Metric.ball c R ∩ {x | g x ≤ a})*(∫ x in Metric.ball c R, dgClamp a b (g x)) ≤
      (2:ℝ)^(2*n+1)*R*volume.real (Metric.ball c R)*
        (∫ x in Metric.ball c R ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ g x‖) := by
  obtain ⟨w,hw,hagree⟩ := dg_ball_smooth_extension hO c R hBO hg
  have hsets (P : ℝ → Prop) : Metric.ball c R ∩ {x | P (w x)} = Metric.ball c R ∩ {x | P (g x)} := by
    ext x
    by_cases hx : x ∈ Metric.ball c R
    · simp only [mem_inter_iff,mem_ofPred_eq,hx,true_and,(hagree x hx).1]
    · simp only [mem_inter_iff,hx,false_and]
  have hh := dg_ball_clamp_zero_set_poincare c hR (hw.of_le (by simp)) hab
  rw [hsets (fun r => r ≤ a),hsets (fun r => a < r ∧ r < b)] at hh
  have hVal : (∫ x in Metric.ball c R, dgClamp a b (w x)) = ∫ x in Metric.ball c R, dgClamp a b (g x) :=
    setIntegral_congr_fun measurableSet_ball (fun x hx => congrArg (dgClamp a b) (hagree x hx).1)
  have hBand : MeasurableSet (Metric.ball c R ∩ {x | a < g x ∧ g x < b}) := by
    rw [←hsets (fun r => a < r ∧ r < b)]
    exact measurableSet_ball.inter ((isOpen_lt continuous_const hw.continuous).measurableSet.inter
      (isOpen_lt hw.continuous continuous_const).measurableSet)
  have hGrad : (∫ x in Metric.ball c R ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ w x‖) =
      ∫ x in Metric.ball c R ∩ {x | a < g x ∧ g x < b}, ‖fderiv ℝ g x‖ :=
    setIntegral_congr_fun hBand (fun x hx => congrArg norm (hagree x hx.1).2)
  simpa only [hVal,hGrad] using hh


/-- This is the usual capped positive part, as an equality of actual functions. -/
theorem dgClamp_eq_min_positivePart {a b : ℝ} (hab : a ≤ b) (r : ℝ) :
    dgClamp a b r = min (dgPositivePart (r-a)) (b-a) := by
  by_cases hra : r ≤ a
  · rw [dgClamp_zero hab hra,dgPositivePart_of_nonpos (by linarith : r-a ≤ 0)]
    exact (min_eq_left (sub_nonneg.mpr hab)).symm
  by_cases hbr : b ≤ r
  · rw [dgClamp_gap hab hbr,dgPositivePart_of_nonneg (by linarith : 0 ≤ r-a)]
    exact (min_eq_right (by linarith)).symm
  rw [dgClamp_middle ⟨lt_of_not_ge hra,lt_of_not_ge hbr⟩,
    dgPositivePart_of_nonneg (by linarith : 0 ≤ r-a)]
  exact (min_eq_left (by linarith)).symm

/-- Actual clipping is Lipschitz with constant one. -/
theorem dgClamp_lipschitz {a b : ℝ} (hab : a ≤ b) : LipschitzWith 1 (dgClamp a b) := by
  have he : dgClamp a b = fun r => min (dgPositivePart (r-a)) (b-a) :=
    funext (dgClamp_eq_min_positivePart hab)
  rw [he]
  have hp : LipschitzWith 1 (fun r : ℝ => dgPositivePart (r-a)) := by
    have hshift : LipschitzWith 1 (fun r : ℝ => r-a) := by
      apply LipschitzWith.of_dist_le_mul
      intro x y
      simp only [NNReal.coe_one,one_mul,Real.dist_eq]
      have he : (x-a)-(y-a) = x-y := by ring
      rw [he]
    simpa only [one_mul,Function.comp_def] using dgPositivePart_lipschitz.comp hshift
  simpa only [max_eq_left (show (0:ℝ≥0) ≤ 1 by positivity)] using hp.min (LipschitzWith.const (b-a))

end Yau.LeafProofs.L16Aux
