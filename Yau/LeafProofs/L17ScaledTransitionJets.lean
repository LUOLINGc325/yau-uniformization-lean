import Yau.LeafProofs.L17TransitionJets
import Yau.LeafProofs.L17DerivativeScaling

/-! Uniform jets after rescaling an actual chart overlap to unit scale. -/

noncomputable section

open Set Metric
open scoped ContDiff

namespace Yau.LeafProofs.L17Aux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

abbrev SmallChartScale := {ρ : ℝ // 0 < ρ ∧ ρ ≤ 1}
abbrev ChartScaleIndex (M : ComplexManifold n) := SmallChartScale × (M.Carrier × M.Carrier)

def BoundedChartFamily.scaledTransitionMap (A : BoundedChartFamily g) (a : ChartScaleIndex M) :
    ComplexVector n → ComplexVector n :=
  fun z => (a.1.val)⁻¹ • A.transitionMap a.2 (a.1.val • z)

def BoundedChartFamily.scaledTransitionPreDomain (A : BoundedChartFamily g)
    (a : ChartScaleIndex M) : Set (ComplexVector n) :=
  (fun z => a.1.val • z) ⁻¹' A.transitionBallDomain a.2

def BoundedChartFamily.scaledTransitionDomain (A : BoundedChartFamily g)
    (a : ChartScaleIndex M) : Set (ComplexVector n) :=
  A.scaledTransitionPreDomain a ∩ A.scaledTransitionMap a ⁻¹' ball 0 2

theorem BoundedChartFamily.scaledTransitionPreDomain_isOpen (A : BoundedChartFamily g)
    (a : ChartScaleIndex M) : IsOpen (A.scaledTransitionPreDomain a) :=
  (A.transitionBallDomain_isOpen a.2).preimage (by fun_prop)

theorem BoundedChartFamily.scaledTransition_base_smooth (A : BoundedChartFamily g)
    (a : ChartScaleIndex M) : ContDiffOn ℝ ∞
      (fun z => A.transitionMap a.2 (a.1.val • z)) (A.scaledTransitionPreDomain a) := by
  have hL : ContDiff ℝ ∞ (fun z : ComplexVector n => a.1.val • z) := by
    convert! (a.1.val • ContinuousLinearMap.id ℝ (ComplexVector n)).contDiff using 1
  exact (A.transitionMap_contDiffOn a.2).comp hL.contDiffOn (fun _ hz => hz)

theorem BoundedChartFamily.scaledTransition_pre_smooth (A : BoundedChartFamily g)
    (a : ChartScaleIndex M) :
    ContDiffOn ℝ ∞ (A.scaledTransitionMap a) (A.scaledTransitionPreDomain a) :=
  (A.scaledTransition_base_smooth a).const_smul _

theorem BoundedChartFamily.scaledTransitionDomain_isOpen (A : BoundedChartFamily g)
    (a : ChartScaleIndex M) : IsOpen (A.scaledTransitionDomain a) :=
  (A.scaledTransition_pre_smooth a).continuousOn.isOpen_inter_preimage
    (A.scaledTransitionPreDomain_isOpen a) isOpen_ball

theorem BoundedChartFamily.scaledTransition_smooth (A : BoundedChartFamily g)
    (a : ChartScaleIndex M) :
    ContDiffOn ℝ ∞ (A.scaledTransitionMap a) (A.scaledTransitionDomain a) :=
  (A.scaledTransition_pre_smooth a).mono inter_subset_left

theorem BoundedChartFamily.scaledTransition_uniformJetBounds
    (A : BoundedChartFamily g) (k : ℕ) :
    UniformJetBounds k A.scaledTransitionMap A.scaledTransitionDomain := by
  obtain ⟨C, hC, hb⟩ := A.transition_uniformJetBounds k
  refine ⟨max 2 C, (by norm_num : (1 : ℝ) ≤ 2).trans (le_max_left _ _), ?_⟩
  intro a z hz j hj
  have hρ : 0 < a.1.val := a.1.property.1
  have hρone : a.1.val ≤ 1 := a.1.property.2
  have hnative : a.1.val • z ∈ A.transitionBallDomain a.2 := hz.1
  cases j with
  | zero =>
    rw [norm_iteratedFDeriv_zero]
    have ht : A.scaledTransitionMap a z ∈ ball 0 2 := hz.2
    have hnorm : ‖A.scaledTransitionMap a z‖ < 2 := by
      simpa only [mem_ball, dist_zero_right] using ht
    exact hnorm.le.trans (le_max_left _ _)
  | succ m =>
    have hAt := ((A.scaledTransition_base_smooth a).contDiffAt
      ((A.scaledTransitionPreDomain_isOpen a).mem_nhds hz.1)).of_le
        (by simp : ((m + 1 : ℕ) : ℕ∞ω) ≤ ∞)
    change ‖iteratedFDeriv ℝ (m + 1)
      (fun w => (a.1.val)⁻¹ • A.transitionMap a.2 (a.1.val • w)) z‖ ≤ max 2 C
    rw [iteratedFDeriv_const_smul_apply' hAt, norm_smul, Real.norm_eq_abs,
      abs_of_pos (inv_pos.mpr hρ)]
    have hcomp := norm_iteratedFDeriv_comp_smul_le (A.transitionBallDomain_isOpen a.2)
      (A.transitionMap_contDiffOn a.2) a.1.val hnative (m + 1)
    rw [Real.norm_eq_abs, abs_of_pos hρ] at hcomp
    have hfactor : (a.1.val)⁻¹ * a.1.val ^ (m + 1) ≤ 1 := by
      calc
        _ = a.1.val ^ m := by rw [pow_succ]; field_simp
        _ ≤ 1 := pow_le_one₀ hρ.le hρone
    calc
      _ ≤ (a.1.val)⁻¹ * (‖iteratedFDeriv ℝ (m + 1) (A.transitionMap a.2)
          (a.1.val • z)‖ * a.1.val ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left hcomp (inv_nonneg.mpr hρ.le)
      _ ≤ (a.1.val)⁻¹ * (C * a.1.val ^ (m + 1)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right (hb a.2 _ hnative _ hj) (by positivity))
          (inv_nonneg.mpr hρ.le)
      _ = C * ((a.1.val)⁻¹ * a.1.val ^ (m + 1)) := by ring
      _ ≤ C * 1 := mul_le_mul_of_nonneg_left hfactor (zero_le_one.trans hC)
      _ ≤ max 2 C := by simpa only [mul_one] using le_max_right 2 C

end Yau.LeafProofs.L17Aux
