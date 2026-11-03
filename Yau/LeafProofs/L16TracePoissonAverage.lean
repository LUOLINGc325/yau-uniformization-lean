import Yau.LeafProofs.L16BoundaryTraceTimeExtension
import Yau.LeafProofs.L16NormalPoissonMoments

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- A simultaneous source-space/time translation survives the heat average
    with exactly the original parabolic Holder budget. -/
theorem heatAverage_parabolic_difference_bound {n : ℕ} {α F : ℝ} (hα : 0 < α)
    {B : Point n → ℝ} (hB : HolderBound α Set.univ B F) {r : ℝ} (hr : 0 < r)
    (p q : Point n) :
    |heatAverage r (fun y => B (y,p.2-r)) p.1 -
      heatAverage r (fun y => B (y,q.2-r)) q.1| ≤ F*holderWeight α p q := by
  have hCont : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hSup (x : Point n) : |B x| ≤ F := hB.2.1 x (Set.mem_univ _)
  let g : Space n → ℝ := fun z => B (p.1+z,p.2-r)-B (q.1+z,q.2-r)
  have hg : Continuous g := by
    exact (hCont.comp ((continuous_const.add continuous_id).prodMk continuous_const)).sub
      (hCont.comp ((continuous_const.add continuous_id).prodMk continuous_const))
  have hG : ∀ z, |g z| ≤ F*holderWeight α p q := by
    intro z
    have h := hB.2.2 (p.1+z,p.2-r) (Set.mem_univ _) (q.1+z,q.2-r) (Set.mem_univ _)
    have hSpace : p.1+z-(q.1+z) = p.1-q.1 := by abel
    have hTime : (p.2-r)-(q.2-r) = p.2-q.2 := by ring
    simpa only [g,Real.norm_eq_abs,holderWeight,hSpace,hTime] using h
  have hI (p' : Point n) : Integrable (fun z : Space n => gaussianKernel r z*B (p'.1-z,p'.2-r)) := by
    apply heatAverage_integrable_of_bounded hr
      (hCont.comp (continuous_id.prodMk continuous_const))
    intro y
    exact hSup (y,p'.2-r)
  have hEq : heatAverage r g 0 =
      heatAverage r (fun y => B (y,p.2-r)) p.1 -
        heatAverage r (fun y => B (y,q.2-r)) q.1 := by
    rw [heatAverage_def,heatAverage_def,heatAverage_def,← integral_sub (hI p) (hI q)]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall fun z => by
      simp only [g,zero_sub,← sub_eq_add_neg,mul_sub]
  rw [← hEq]
  exact heatAverage_bound hr hg hG 0

/-- The actual positive parabolic Poisson average. -/
def tracePoissonAverage {n : ℕ} (a : ℝ) (B : Point n → ℝ) (p : Point n) : ℝ :=
  if a = 0 then B p else
    ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*
      heatAverage r (fun y => B (y,p.2-r)) p.1

theorem retardedHeatAverage_aestronglyMeasurable {n : ℕ} {B : Point n → ℝ}
    (hB : Continuous B) (p : Point n) :
    AEStronglyMeasurable (fun r : ℝ => heatAverage r (fun y => B (y,p.2-r)) p.1)
      (volume.restrict (Set.Ioi 0)) := by
  have hF : Measurable (fun z : ℝ × Space n =>
      gaussianKernel z.1 z.2*B (p.1-z.2,p.2-z.1)) := by
    exact (gaussianKernel_joint_measurable (n := n)).mul
      (hB.measurable.comp (by fun_prop))
  simpa only [heatAverage_def,Function.uncurry_apply_pair] using
    (hF.aestronglyMeasurable (μ := (volume.restrict (Set.Ioi 0)).prod volume)).integral_prod_right'

theorem normalPoissonKernel_measurable (a : ℝ) : Measurable (normalPoissonKernel a) := by
  change Measurable (fun r : ℝ => (a/r)*((Real.sqrt (4*Real.pi*r))⁻¹*
    Real.exp (-(4*r)⁻¹*a^2)))
  fun_prop

theorem tracePoissonAverage_integrable {n : ℕ} {a F : ℝ} (ha : 0 < a)
    {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (p : Point n) :
    IntegrableOn (fun r => normalPoissonKernel a r*
      heatAverage r (fun y => B (y,p.2-r)) p.1) (Set.Ioi 0) := by
  have hProb := normalPoissonKernel_probability ha
  have hm := (normalPoissonKernel_measurable a).aestronglyMeasurable.mul
    (retardedHeatAverage_aestronglyMeasurable hB p)
  apply (hProb.1.mul_const F).mono' hm
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
  have hHeat := heatAverage_bound hr
    (hB.comp (continuous_id.prodMk continuous_const))
    (fun y => hF (y,p.2-r)) p.1
  have hPos := normalPoissonKernel_nonneg ha.le hr
  simp only [Pi.mul_apply]
  rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg hPos]
  exact mul_le_mul_of_nonneg_left hHeat hPos

theorem tracePoissonAverage_bound {n : ℕ} {a F : ℝ} (ha : 0 ≤ a)
    {B : Point n → ℝ} (hB : Continuous B) (hF : ∀ p, |B p| ≤ F) (p : Point n) :
    |tracePoissonAverage a B p| ≤ F := by
  by_cases ha0 : a = 0
  · simpa only [tracePoissonAverage,ite_eq_left ha0] using hF p
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hProb := normalPoissonKernel_probability haPos
  have hInt := tracePoissonAverage_integrable haPos hB hF p
  have hDom : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖normalPoissonKernel a r*heatAverage r (fun y => B (y,p.2-r)) p.1‖ ≤
        normalPoissonKernel a r*F := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    have hHeat := heatAverage_bound hr
      (hB.comp (continuous_id.prodMk continuous_const))
      (fun y => hF (y,p.2-r)) p.1
    rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (normalPoissonKernel_nonneg ha hr)]
    exact mul_le_mul_of_nonneg_left hHeat (normalPoissonKernel_nonneg ha hr)
  rw [tracePoissonAverage,ite_eq_right ha0]
  calc
    |∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*
        heatAverage r (fun y => B (y,p.2-r)) p.1| ≤
        ∫ r in Set.Ioi (0 : ℝ), ‖normalPoissonKernel a r*
          heatAverage r (fun y => B (y,p.2-r)) p.1‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (fun r => normalPoissonKernel a r*heatAverage r (fun y => B (y,p.2-r)) p.1)
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*F :=
      integral_mono_ae hInt.norm (hProb.1.mul_const F) hDom
    _ = F := by rw [integral_mul_const,hProb.2,one_mul]


theorem tracePoissonAverage_fixed_normal_holder {n : ℕ} {α F a : ℝ}
    (hα : 0 < α) (ha : 0 ≤ a) {B : Point n → ℝ}
    (hB : HolderBound α Set.univ B F) :
    HolderBound α Set.univ (tracePoissonAverage a B) F := by
  by_cases ha0 : a = 0
  · have hEq : tracePoissonAverage a B = B := by
      funext p
      exact ite_eq_left ha0
    rw [hEq]
    exact hB
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hCont : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hSup : ∀ p, |B p| ≤ F := fun p => hB.2.1 p (Set.mem_univ _)
  have hProb := normalPoissonKernel_probability haPos
  refine ⟨hB.1,fun p _hp => tracePoissonAverage_bound ha hCont hSup p,?_⟩
  intro p _hp q _hq
  have hIp := tracePoissonAverage_integrable haPos hCont hSup p
  have hIq := tracePoissonAverage_integrable haPos hCont hSup q
  have hDiffInt := hIp.sub hIq
  have hDom : ∀ᵐ r ∂volume.restrict (Set.Ioi (0 : ℝ)),
      ‖normalPoissonKernel a r*heatAverage r (fun y => B (y,p.2-r)) p.1 -
        normalPoissonKernel a r*heatAverage r (fun y => B (y,q.2-r)) q.1‖ ≤
        normalPoissonKernel a r*(F*holderWeight α p q) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
    rw [← mul_sub,Real.norm_eq_abs,abs_mul,
      abs_of_nonneg (normalPoissonKernel_nonneg ha hr)]
    exact mul_le_mul_of_nonneg_left (heatAverage_parabolic_difference_bound hα hB hr p q)
      (normalPoissonKernel_nonneg ha hr)
  rw [tracePoissonAverage,ite_eq_right ha0,tracePoissonAverage,ite_eq_right ha0,
    ← integral_sub hIp hIq]
  calc
    |∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*
        heatAverage r (fun y => B (y,p.2-r)) p.1-
        normalPoissonKernel a r*heatAverage r (fun y => B (y,q.2-r)) q.1| ≤
        ∫ r in Set.Ioi (0 : ℝ), ‖normalPoissonKernel a r*
          heatAverage r (fun y => B (y,p.2-r)) p.1-
          normalPoissonKernel a r*heatAverage r (fun y => B (y,q.2-r)) q.1‖ := by
      simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
        (μ := volume.restrict (Set.Ioi (0 : ℝ)))
        (fun r => normalPoissonKernel a r*heatAverage r (fun y => B (y,p.2-r)) p.1-
          normalPoissonKernel a r*heatAverage r (fun y => B (y,q.2-r)) q.1)
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*(F*holderWeight α p q) :=
      integral_mono_ae hDiffInt.norm (hProb.1.mul_const _) hDom
    _ = F*holderWeight α p q := by rw [integral_mul_const,hProb.2,one_mul]


theorem retardedHeatAverage_sub_source_bound {n : ℕ} {α : ℝ} (hα : 0 < α) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F : ℝ),
      HolderBound α Set.univ B F → ∀ r : ℝ, 0 < r → ∀ p : Point n,
      |heatAverage r (fun y => B (y,p.2-r)) p.1-B p| ≤ C*F*r^(α/2) := by
  obtain ⟨C,hC,hAvg⟩ := heatAverage_sub_initial_holder_bound (n := n) hα.le
  refine ⟨C+1,by linarith,?_⟩
  intro B F hB r hr p
  have hCont : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hSpace : ∀ x y : Space n,
      |B (x,p.2-r)-B (y,p.2-r)| ≤ F*‖x-y‖^α := by
    intro x y
    have h := hB.2.2 (x,p.2-r) (Set.mem_univ _) (y,p.2-r) (Set.mem_univ _)
    simpa only [Real.norm_eq_abs,holderWeight,sub_self,abs_zero,
      Real.zero_rpow (by positivity : α/2 ≠ 0),add_zero] using h
  have hHeat := hAvg r hr (fun y => B (y,p.2-r)) F F
    (hCont.comp (continuous_id.prodMk continuous_const))
    (fun y => hB.2.1 (y,p.2-r) (Set.mem_univ _)) hB.1 hSpace p.1
  have hTime : |B (p.1,p.2-r)-B p| ≤ F*r^(α/2) := by
    have h := hB.2.2 (p.1,p.2-r) (Set.mem_univ _) p (Set.mem_univ _)
    have hDiff : (p.2-r)-p.2 = -r := by ring
    simpa only [Real.norm_eq_abs,holderWeight,sub_self,norm_zero,
      Real.zero_rpow hα.ne',zero_add,hDiff,abs_neg,abs_of_pos hr] using h
  calc
    |heatAverage r (fun y => B (y,p.2-r)) p.1-B p| ≤
        |heatAverage r (fun y => B (y,p.2-r)) p.1-B (p.1,p.2-r)|+
          |B (p.1,p.2-r)-B p| := abs_sub_le _ _ _
    _ ≤ (C+1)*F*r^(α/2) := by linarith

/-- The real Poisson average tends to its boundary trace with the correct
    fractional normal-distance modulus, uniformly in the source. -/
theorem tracePoissonAverage_sub_source_bound {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (B : Point n → ℝ) (F : ℝ),
      HolderBound α Set.univ B F → ∀ a : ℝ, 0 ≤ a → ∀ p : Point n,
      |tracePoissonAverage a B p-B p| ≤ C*F*a^α := by
  obtain ⟨CH,hCH,hHeat⟩ := retardedHeatAverage_sub_source_bound (n := n) hα
  obtain ⟨CM,hCM,hMoment⟩ := normalPoissonKernel_weighted_moment hα hα1
  refine ⟨CH*CM,by positivity,?_⟩
  intro B F hB a ha p
  by_cases ha0 : a = 0
  · simp only [tracePoissonAverage,ite_eq_left ha0,sub_self,abs_zero]
    exact mul_nonneg (mul_nonneg (mul_nonneg hCH.le hCM.le) hB.1)
      (Real.rpow_nonneg ha α)
  have haPos : 0 < a := lt_of_le_of_ne ha (Ne.symm ha0)
  have hCont : Continuous B := continuousOn_univ.mp (holderBound_continuousOn hα hB)
  have hSup : ∀ q, |B q| ≤ F := fun q => hB.2.1 q (Set.mem_univ _)
  have hProb := normalPoissonKernel_probability haPos
  have hIp := tracePoissonAverage_integrable haPos hCont hSup p
  have hIc := hProb.1.mul_const (B p)
  have hEq : tracePoissonAverage a B p-B p =
      ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*
        (heatAverage r (fun y => B (y,p.2-r)) p.1-B p) := by
    rw [tracePoissonAverage,ite_eq_right ha0]
    calc
      _ = (∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*
          heatAverage r (fun y => B (y,p.2-r)) p.1)-
          ∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*B p := by
        rw [integral_mul_const,hProb.2,one_mul]
      _ = _ := by
        rw [← integral_sub hIp hIc]
        apply integral_congr_ae
        exact Filter.Eventually.of_forall fun r => by ring
  have hMom := hMoment a haPos
  rw [hEq,← Real.norm_eq_abs]
  calc
    _ ≤ ∫ r in Set.Ioi (0 : ℝ), (CH*F)*(normalPoissonKernel a r*r^(α/2)) := by
      apply norm_integral_le_of_norm_le (hMom.1.const_mul (CH*F))
      filter_upwards [ae_restrict_mem measurableSet_Ioi] with r hr
      rw [Real.norm_eq_abs,abs_mul,abs_of_nonneg (normalPoissonKernel_nonneg ha hr)]
      have h := mul_le_mul_of_nonneg_left (hHeat B F hB r hr p)
        (normalPoissonKernel_nonneg ha hr)
      convert h using 1 <;> ring
    _ = (CH*F)*(∫ r in Set.Ioi (0 : ℝ), normalPoissonKernel a r*r^(α/2)) :=
      integral_const_mul _ _
    _ ≤ (CH*F)*(CM*a^α) := mul_le_mul_of_nonneg_left hMom.2 (mul_nonneg hCH.le hB.1)
    _ = (CH*CM)*F*a^α := by ring

end Yau.LeafProofs.L16Aux
