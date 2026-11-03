import Yau.Proofs.F05BackgroundBounds
import Yau.Proofs.F05GeneralInitial

/-! Nonconstant-profile compatibility supplies the same genuine small source
norm for the actual nonlinear correction at positive-time restart. -/

open Set
open scoped ContDiff
noncomputable section
set_option maxHeartbeats 2600000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_zero_source_small_general {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ)
    {S : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S)) (hp : SmoothSpaceTime p (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (hCompat : ∀ x, derivWithin (p x) (Icc 0 S) 0 =
      Real.exp (-p x 0)*laplacian (h 0) (fun y => p y 0) x+
        (1-Real.exp (-p x 0))*scalarCurvature (h 0) x) :
    ∃ F₀ : ℝ, 0 < F₀ ∧ ∀ (α : ℝ), 0 < α → α < 1 → ∀ (T : ℝ), 0 < T → T ≤ S → T ≤ 1 →
      ∀ i, HolderBound α (F05Q A i T) (pull A i (F05NonlinearCorrection h T p (fun _ _ => 0)))
        (F₀*T^((1-α)/2)) := by
  classical
  have hFixed0 (x : M.Carrier) : F05NonlinearCorrection h S p (fun _ _ => 0) x 0 = 0 :=
    F05_nonlinear_initial_general h S p _ (fun _ => rfl) hCompat x
  choose C hC hBudget using (fun i : Fin A.count => F05_compact_cylinder_holder_zero Metric.isOpen_ball
    (isCompact_closedBall (0 : Space n) 2) (convex_closedBall (0 : Space n) 2)
    (Metric.closedBall_subset_ball (by norm_num : (2 : ℝ) < 3)) hS
    (F05_pull_zero_source_smooth hA h p hS hh hp hR i) (fun z _ => hFixed0 (lift A i z)))
  let F₀ := 1+∑ i,C i
  have hSum : 0 ≤ ∑ i,C i := Finset.sum_nonneg (fun i _ => (hC i).le)
  refine ⟨F₀,by dsimp only [F₀]; positivity,?_⟩
  intro α hα hα1 T hT hTS hT1 i
  have hCF : C i ≤ F₀ := by
    have hh := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => (hC j).le)
      (Finset.mem_univ i)
    dsimp only [F₀]
    linarith
  have hSub : F05Q A i T ⊆ cylinder (Metric.closedBall 0 2) 0 T := fun q hq =>
    ⟨by simpa only [Metric.mem_closedBall,dist_zero_right] using hq.1.1,hq.2⟩
  have hBound := holderBound_mono (hBudget i α hα hα1 T hT hTS hT1) hSub
  have hActual := holderBound_congr_on hBound (fun q hq =>
    (F05_nonlinear_zero_restrict hA h p hp hT hTS i ⟨F05D_mem_ball hq.1,hq.2⟩).symm)
  exact holderBound_mono_const hActual (mul_le_mul_of_nonneg_right hCF (Real.rpow_nonneg hT.le _))

end Yau.Proofs.F05Aux
