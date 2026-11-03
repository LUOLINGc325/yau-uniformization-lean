import Yau.Proofs.F01AffineLinearEquation

/-! The original interior estimate applies to the actually rescaled
equation, with its unchanged matrix, computed rescaled source and genuine
closed-face C2 data. Its estimate parameter will be discharged by the
original L16 producer; no solution or higher-regularity oracle is used. -/
noncomputable section
open Set
open scoped ContDiff Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.ParabolicCandidates
variable {n : ℕ}

theorem holderBound_restrict {E : Type*} [NormedAddCommGroup E]
    {Q Q' : Set (Point n)} {β C : ℝ} {f : Point n → E}
    (hf : HolderBound β Q f C) (hQ : Q' ⊆ Q) : HolderBound β Q' f C :=
  ⟨hf.1, fun p hp => hf.2.1 p (hQ hp),
    fun p hp q hq => hf.2.2 p (hQ hp) q (hQ hq)⟩

theorem interior_schauder_affine_transfer
    (hInterior : InteriorLinearSchauder) (hn : 0 < n)
    {β ell upper M : ℝ} (hβ : 0 < β) (hβ1 : β < 1) (hM : 0 < M) :
    ∃ C : ℝ, 0 < C ∧ ∀ (S : Set (Space n)) (l r ρ τ : ℝ) (c : Space n)
      (A : Point n → Mat n) (u f : Point n → ℝ) (F B : ℝ),
      |ρ| ≤ 1 →
      MapsTo (fun x => ρ • x + c) (Metric.ball 0 2) S →
      MapsTo (fun t => τ + ρ ^ 2 * t) (Icc (-4) 0) (Icc l r) →
      Elliptic (cylinder S l r) A ell upper →
      HolderBound β (cylinder S l r) A M →
      HolderBound β (cylinder S l r) f F → C2 (cylinder S l r) u →
      (∀ p ∈ cylinder S l r, |u p| ≤ B) →
      (∀ p ∈ cylinder S l r, linearOp (cylinder S l r) A (fun _ _ => 0) u p = f p) →
      SchauderBound β (backward 1) (affineParabolicPullback ρ c τ u) (C * (B + F)) := by
  obtain ⟨C, hC, hc⟩ := hInterior n hn β ell upper M hβ hβ1 hM
  refine ⟨C, hC, ?_⟩
  intro S l r ρ τ c A u f F B hρ hSpace hClock hEll hA hf hu hSup hEq
  have hClock' : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc (-((2 : ℝ) ^ 2)) 0) (Icc l r) := by
    norm_num at hClock ⊢
    exact hClock
  have hSub : backward (n := n) (2 : ℝ) ⊆
      cylinder (Metric.ball (0 : Space n) 2) (-4) 0 := by
    intro p hp
    exact ⟨hp.1, by nlinarith [hp.2.1], hp.2.2⟩
  have hMap : MapsTo (affineParabolicPoint ρ c τ) (backward 2) (cylinder S l r) :=
    fun p hp => ⟨hSpace hp.1, hClock (hSub hp).2⟩
  have hCoeff := holderBound_affineParabolicPullback hρ hβ.le hMap hA
  have hSource := holderBound_real_smul_of_abs_le_one
    (holderBound_affineParabolicPullback hρ hβ.le hMap hf)
    ((by simpa only [abs_of_nonneg (sq_nonneg ρ)] using
      (sq_le_one_iff_abs_le_one ρ).mpr hρ) : |ρ ^ 2| ≤ 1)
  have hC2 := c2_closed_open_lower
    (c2_affineParabolicPullback (by norm_num : (-4 : ℝ) < 0) hu hSpace hClock)
  have hDrift (i : RIdx n) : HolderBound β (backward (n := n) (2 : ℝ))
      (fun _ : Point n => (0 : ℝ)) M := by
    refine ⟨hM.le, fun _ _ => by simpa only [norm_zero] using hM.le, ?_⟩
    intro p hp q hq
    simp only [sub_self, norm_zero]
    exact mul_nonneg hM.le (by unfold holderWeight; positivity)
  apply hc (fun q => A (affineParabolicPoint ρ c τ q)) (fun _ _ => 0)
    (fun p => ρ ^ 2 * f (affineParabolicPoint ρ c τ p))
    (affineParabolicPullback ρ c τ u) F B
    (elliptic_comp_mapsTo hEll hMap) hCoeff hDrift
  · simpa only [smul_eq_mul] using hSource
  · simpa only [backward, show -((2 : ℝ) ^ 2) = -4 by norm_num] using hC2
  · intro p hp
    exact hSup _ (hMap hp)
  · exact affineParabolicPullback_backward_equation A f (by norm_num : (0 : ℝ) < 2)
      hu hSpace hClock' hEq

end Yau.NodeProofs.F01Aux
