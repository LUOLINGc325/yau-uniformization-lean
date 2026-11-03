import Yau.LeafProofs.L16LocalizedClassicalEquation

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem smoothTransition_deriv_hasCompactSupport :
    HasCompactSupport (deriv Real.smoothTransition) := by
  apply HasCompactSupport.of_support_subset_isCompact (isCompact_Icc (a := (0 : ℝ)) (b := 1))
  intro x hx
  by_contra hOutside
  have hZero : deriv Real.smoothTransition x = 0 := by
    by_cases hx0 : x < 0
    · have hEq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => 0) := by
        filter_upwards [Iio_mem_nhds hx0] with y hy
        exact Real.smoothTransition.zero_of_nonpos hy.le
      simpa using hEq.deriv_eq
    · have hx1 : 1 < x := by
        have hNot : ¬ (0 ≤ x ∧ x ≤ 1) := hOutside
        exact lt_of_not_ge ((not_and.mp hNot) (le_of_not_gt hx0))
      have hEq : Real.smoothTransition =ᶠ[𝓝 x] (fun _ => 1) := by
        filter_upwards [Ioi_mem_nhds hx1] with y hy
        exact Real.smoothTransition.one_of_one_le hy.le
      simpa using hEq.deriv_eq
  exact hx hZero

theorem smoothTransition_two_derivative_bounds :
    ∃ C : ℝ, 1 ≤ C ∧
      (∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C) ∧
      (∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ C) ∧
      (∀ x y : ℝ, |Real.smoothTransition x-Real.smoothTransition y| ≤ C*|x-y|) ∧
      (∀ x y : ℝ, |deriv Real.smoothTransition x-deriv Real.smoothTransition y| ≤ C*|x-y|) := by
  have hSmooth : ContDiff ℝ 3 Real.smoothTransition := Real.smoothTransition.contDiff
  have hDeriv : ContDiff ℝ 2 (deriv Real.smoothTransition) := hSmooth.deriv'
  obtain ⟨A,hA⟩ := smoothTransition_deriv_hasCompactSupport.exists_bound_of_continuous hDeriv.continuous
  obtain ⟨D,hD⟩ := smoothTransition_deriv_hasCompactSupport.deriv.exists_bound_of_continuous
    (hDeriv.continuous_deriv (by norm_num))
  let C : ℝ := 1+|A|+|D|
  have hC : 1 ≤ C := by dsimp only [C]; linarith [abs_nonneg A,abs_nonneg D]
  have hAC : A ≤ C := by dsimp only [C]; linarith [le_abs_self A,abs_nonneg D]
  have hDC : D ≤ C := by dsimp only [C]; linarith [le_abs_self D,abs_nonneg A]
  have h1 (x : ℝ) : |deriv Real.smoothTransition x| ≤ C := (hA x).trans hAC
  have h2 (x : ℝ) : |deriv (deriv Real.smoothTransition) x| ≤ C := (hD x).trans hDC
  refine ⟨C,hC,h1,h2,?_,?_⟩
  · intro x y
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (Set.univ : Set ℝ)) =>
        (hSmooth.differentiable (by norm_num) z).hasDerivAt.hasDerivWithinAt)
      (fun z _ => h1 z) convex_univ (Set.mem_univ y) (Set.mem_univ x)
  · intro x y
    simpa only [Real.norm_eq_abs] using Convex.norm_image_sub_le_of_norm_hasDerivWithin_le
      (fun z (_ : z ∈ (Set.univ : Set ℝ)) =>
        (hDeriv.differentiable (by norm_num) z).hasDerivAt.hasDerivWithinAt)
      (fun z _ => h2 z) convex_univ (Set.mem_univ y) (Set.mem_univ x)

def initialTimeCutoff (T : ℝ) (t : ℝ) : ℝ :=
  Real.smoothTransition ((4/T)*t-1)

theorem initialTimeCutoff_contDiff (T : ℝ) : ContDiff ℝ ∞ (initialTimeCutoff T) := by
  unfold initialTimeCutoff
  fun_prop

theorem initialTimeCutoff_deriv (T t : ℝ) :
    deriv (initialTimeCutoff T) t = (4/T)*deriv Real.smoothTransition ((4/T)*t-1) := by
  have hSmooth : ContDiff ℝ 1 Real.smoothTransition := Real.smoothTransition.contDiff
  have hAffine : HasDerivAt (fun x : ℝ => (4/T)*x-1) (4/T) t := by
    convert ((hasDerivAt_id t).const_mul (4/T)).sub_const 1 using 1 <;> simp
  have hComp := (hSmooth.differentiable (by norm_num)
    ((4/T)*t-1)).hasDerivAt.comp t hAffine
  have hResult : HasDerivAt (initialTimeCutoff T)
      (deriv Real.smoothTransition ((4/T)*t-1)*(4/T)) t := hComp
  exact hResult.deriv.trans (mul_comm _ _)

theorem initialTimeCutoff_mem_Icc (T t : ℝ) : initialTimeCutoff T t ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨Real.smoothTransition.nonneg _,Real.smoothTransition.le_one _⟩

theorem initialTimeCutoff_initial (T : ℝ) : initialTimeCutoff T 0 = 0 := by
  apply Real.smoothTransition.zero_of_nonpos
  simp

theorem initialTimeCutoff_eq_one {T t : ℝ} (hT : 0 < T) (ht : T/2 ≤ t) :
    initialTimeCutoff T t = 1 := by
  apply Real.smoothTransition.one_of_one_le
  have hRatio : (4/T)*t = (4*t)/T := by ring
  rw [hRatio]
  have h : 2 ≤ (4*t)/T := (le_div_iff₀ hT).mpr (by linarith)
  linarith

theorem initialTimeCutoff_uniform_holder_jets {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, 0 < T → T ≤ 1 →
      HolderBound α (cylinder (n := n) Set.univ 0 T)
        (fun p => initialTimeCutoff T p.2) (C/T^2) ∧
      HolderBound α (cylinder (n := n) Set.univ 0 T)
        (fun p => deriv (initialTimeCutoff T) p.2) (C/T^2) := by
  obtain ⟨D,hD,hD1,hD2,hLip0,hLip1⟩ := smoothTransition_two_derivative_bounds
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  have hD0 : 0 ≤ D := hDpos.le
  refine ⟨32*D,by positivity,?_⟩
  intro T hT hT1
  let L : ℝ := 16*D/T^2
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  have hScale : 0 < 4/T := by positivity
  have hSmall : 4*D/T ≤ L := by
    dsimp only [L]
    apply (div_le_div_iff₀ hT (sq_pos_of_pos hT)).mpr
    have hSq : T^2 ≤ T := by nlinarith
    have h := mul_le_mul_of_nonneg_left hSq (by positivity : 0 ≤ 4*D)
    nlinarith [mul_nonneg hD0 hT.le]
  have hOne : 1 ≤ L := by
    dsimp only [L]
    apply (le_div_iff₀ (sq_pos_of_pos hT)).mpr
    have hSq : T^2 ≤ 1 := by nlinarith
    nlinarith
  have hArg (s t : ℝ) : (4/T)*s-1-((4/T)*t-1) = (4/T)*(s-t) := by ring
  have hSup0 (t : ℝ) : |initialTimeCutoff T t| ≤ L := by
    rw [abs_of_nonneg (initialTimeCutoff_mem_Icc T t).1]
    exact (initialTimeCutoff_mem_Icc T t).2.trans hOne
  have hSup1 (t : ℝ) : |deriv (initialTimeCutoff T) t| ≤ L := by
    rw [initialTimeCutoff_deriv,abs_mul,abs_of_pos hScale]
    calc
      _ ≤ (4/T)*D := mul_le_mul_of_nonneg_left (hD1 _) hScale.le
      _ = 4*D/T := by ring
      _ ≤ L := hSmall
  have hLipΘ (s t : ℝ) :
      |initialTimeCutoff T s-initialTimeCutoff T t| ≤ L*|s-t| := by
    have h := hLip0 ((4/T)*s-1) ((4/T)*t-1)
    rw [hArg,abs_mul,abs_of_pos hScale] at h
    calc
      _ ≤ D*((4/T)*|s-t|) := h
      _ = (4*D/T)*|s-t| := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right hSmall (abs_nonneg _)
  have hLipDΘ (s t : ℝ) :
      |deriv (initialTimeCutoff T) s-deriv (initialTimeCutoff T) t| ≤ L*|s-t| := by
    rw [initialTimeCutoff_deriv,initialTimeCutoff_deriv,← mul_sub,abs_mul,abs_of_pos hScale]
    have h := hLip1 ((4/T)*s-1) ((4/T)*t-1)
    rw [hArg,abs_mul,abs_of_pos hScale] at h
    calc
      _ ≤ (4/T)*(D*((4/T)*|s-t|)) := mul_le_mul_of_nonneg_left h hScale.le
      _ = L*|s-t| := by dsimp only [L]; field_simp; ring
  have hMake (g : ℝ → ℝ) (hSup : ∀ t, |g t| ≤ L)
      (hLip : ∀ s t, |g s-g t| ≤ L*|s-t|) :
      HolderBound α (cylinder (n := n) Set.univ 0 T) (fun p => g p.2) (2*L) := by
    have h := holderBound_of_small_lipschitz (n := n) (T := T) (f := fun p : Point n => g p.2)
      (r := 1) (L := L) hα hα1
      (by norm_num) (by norm_num) hL
      (fun p hp => by simpa only [Real.norm_eq_abs,mul_one] using hSup p.2)
      (fun x y t ht => by
        simp only [sub_self,norm_zero]
        exact mul_nonneg hL (norm_nonneg _))
      (fun x s t hs ht => by simpa only [Real.norm_eq_abs] using hLip s t)
    simpa only [Real.one_rpow,mul_one] using h
  constructor
  · convert hMake (initialTimeCutoff T) hSup0 hLipΘ using 1
    dsimp only [L]
    ring
  · convert hMake (deriv (initialTimeCutoff T)) hSup1 hLipDΘ using 1
    dsimp only [L]
    ring

end Yau.LeafProofs.L16Aux
