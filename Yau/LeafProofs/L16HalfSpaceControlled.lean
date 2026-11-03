import Yau.LeafProofs.L16HalfSpaceLinearity
import Yau.LeafProofs.L16ZeroInitialSchauderJets

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic
local instance halfSpaceControlled_dualGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceControlled_dualSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceControlled_hessianGroup {n : ℕ} : NormedAddCommGroup (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance
local instance halfSpaceControlled_hessianSpace {n : ℕ} : NormedSpace ℝ (Space n →L[ℝ] Space n →L[ℝ] ℝ) := inferInstance

theorem halfSpaceConstantPullbackDuhamel_smul {n : ℕ} (B : Space n ≃L[ℝ] Space n)
    (e : Space n) (T c : ℝ) (f : Point n → ℝ) (p : Point n) :
    halfSpaceConstantPullbackDuhamel B e T (c • f) p =
      c*halfSpaceConstantPullbackDuhamel B e T f p :=
  halfSpaceHeatDuhamel_smul _ T c _ _

theorem halfSpaceConstantPullbackDuhamel_add {n : ℕ} {α T F G : ℝ}
    (hα : 0 < α) (hT : 0 ≤ T) (B : Space n ≃L[ℝ] Space n)
    {e : Space n} (he : ‖e‖ = 1) {f g : Point n → ℝ}
    (hf : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F)
    (hg : HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) g G)
    {p : Point n} (hpT : p.2 ∈ Icc 0 T) :
    halfSpaceConstantPullbackDuhamel B e T (f+g) p =
      halfSpaceConstantPullbackDuhamel B e T f p+halfSpaceConstantPullbackDuhamel B e T g p := by
  have hMap : MapsTo (B : Space n →L[ℝ] Space n)
      {x | 0 ≤ inner ℝ (halfSpacePullbackNormal B e) x} {x | 0 ≤ inner ℝ e x} :=
    fun x hx => (halfSpacePullbackNormal_nonneg_iff B he x).mpr hx
  have hF := holderBound_comp_spaceLinearMap_on hα.le (B : Space n →L[ℝ] Space n) hMap hf
  have hG := holderBound_comp_spaceLinearMap_on hα.le (B : Space n →L[ℝ] Space n) hMap hg
  change halfSpaceHeatDuhamel (halfSpacePullbackNormal B e) T (spaceTimePullback B (f+g))
      (B.symm p.1,p.2) = _
  have hPull : spaceTimePullback B (f+g) = spaceTimePullback B f+spaceTimePullback B g := rfl
  rw [hPull]
  exact halfSpaceHeatDuhamel_add hα hT (halfSpacePullbackNormal_unit B he) hF hG hpT

/-- The actual half-space solver has the same controlled full/high/low jet
    interface as the proved whole-space solver. Small jets are derived from
    the full ambient Schauder theorem and its true zero initial slice. -/
theorem halfSpaceConstantPullbackDuhamel_controlled_bounds {n : ℕ} {α : ℝ}
    (hα : 0 < α) (hα1 : α < 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℝ) (B : Space n ≃L[ℝ] Space n),
      constantHeatNormFactor α B ≤ N → ∀ A : Mat n,
      (∀ H : Space n →L[ℝ] Space n →L[ℝ] ℝ,
        (∑ k : Yau.RIdx n, H (B (Yau.realVec k)) (B (Yau.realVec k))) =
          ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, A i j*H (Yau.realVec i) (Yau.realVec j)) →
      ∀ e : Space n, ‖e‖ = 1 → ∀ T F : ℝ, 0 < T → T ≤ 1 → ∀ f : Point n → ℝ,
      HolderBound α (cylinder {x | 0 ≤ inner ℝ e x} 0 T) f F →
      (∀ x, inner ℝ e x = 0 → f (x,0) = 0) →
      let u := halfSpaceConstantPullbackDuhamel B e T f
      SchauderBound α (cylinder univ 0 T) u (C*F*N) ∧
      (∀ p ∈ cylinder univ 0 T, ‖spatialDD u p‖ ≤ C*F*N*T^(α/2)) ∧
      HolderBound α (cylinder univ 0 T) (fun p => (u p,spatialD u p))
        (C*F*N*(T^(1/2 : ℝ)+T^((1-α)/2))) := by
  obtain ⟨C0,hC0,hSolve⟩ := halfSpace_constantPullback_schauder_solution (n := n) hα hα1
  refine ⟨16*C0,by positivity,?_⟩
  intro N B hN A hGram e he T F hT hT1 f hf hCorner
  obtain ⟨hU,hU0,hUB,hPDE⟩ := hSolve B A hGram e he T F hT hT1 f hf hCorner
  have hF : 0 ≤ F := hf.1
  have hFactor : 0 ≤ constantHeatNormFactor α B := (constantHeatNormFactor_pos α B).le
  have hN0 : 0 ≤ N := hFactor.trans hN
  have hBudget : C0*F*constantHeatNormFactor α B ≤ (16*C0)*F*N := by
    calc
      _ ≤ C0*F*N := mul_le_mul_of_nonneg_left hN (mul_nonneg hC0.le hF)
      _ ≤ _ := by nlinarith [mul_nonneg (mul_nonneg hC0.le hF) hN0]
  have hρ : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT
  have hρ1 : Real.sqrt T ≤ 1 := Real.sqrt_le_one.mpr hT1
  have hTρ : T ≤ (Real.sqrt T)^2 := (Real.sq_sqrt hT.le).ge
  have hLow := zero_initial_schauder_lowPair_small hα hα1 hT hρ hρ1 hTρ hU hU0
  have hPower : (Real.sqrt T)^(1-α) = T^((1-α)/2) := by
    rw [Real.sqrt_eq_rpow,← Real.rpow_mul hT.le]
    congr 1
    ring
  rw [hPower] at hLow
  refine ⟨schauderBound_mono_const hU hBudget,?_,?_⟩
  · intro p hp
    exact ((zero_initial_schauder_small_sup hα hT hU hU0 p hp).2).trans
      (mul_le_mul_of_nonneg_right hBudget (by positivity))
  · apply holderBound_mono_const hLow
    have hScale : 16*(C0*F*constantHeatNormFactor α B) ≤ (16*C0)*F*N := by
      nlinarith [mul_le_mul_of_nonneg_left hN (mul_nonneg hC0.le hF)]
    calc
      _ ≤ ((16*C0)*F*N)*T^((1-α)/2) := mul_le_mul_of_nonneg_right hScale (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (by positivity)) (by positivity)

end Yau.LeafProofs.L16Aux
