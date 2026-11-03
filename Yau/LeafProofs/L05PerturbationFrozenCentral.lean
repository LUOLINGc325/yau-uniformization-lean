import Yau.LeafProofs.L05PerturbationFrozenCentralSchauder
import Yau.LeafProofs.L05PerturbationActualEquation
import Yau.LeafProofs.L05PerturbationTaylor

open Filter Set Metric
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

/-- A finite central consequence of the complete original autonomous endpoint.
The analytic input is exactly that tracked endpoint, not a stronger provider. -/
theorem perturb_frozen_central_schauder_of_autonomous
    (hAuto : ∀ n : ℕ, 0 < n → ∀ ell L : ℝ, 0 < ell → ell ≤ L →
      ∃ eta C : ℝ, 0 < eta ∧ eta < 1 ∧ 0 < C ∧
        ∀ F : Sym n → ℝ, Continuous F → globalElliptic F ell L →
          ConcaveOn ℝ univ F → F 0=0 → ∀ u : Point n → ℝ,
          ContinuousOn u (unitClosed n) → (∀ p∈unitClosed n, |u p| ≤ 1) →
          viscositySolution (unitOpen n) (fun H _ => F H) (fun _ => 0) u →
          SchauderBound eta (backward (1/2)) u C)
    (n : ℕ) (hn : 0 < n) (ell L : ℝ) (hell : 0 < ell) (hL : ell ≤ L) :
    ∃ eta0 K : ℝ, 0 < eta0 ∧ eta0 < 1 ∧ 1 < K ∧
      ∀ (F : Sym n → ℝ) (h : Point n → ℝ),
      Continuous F → globalElliptic F ell L → ConcaveOn ℝ Set.univ F → F 0=0 →
      ContinuousOn h (perturbClosed (0 : Space n) (1/2) 0) →
      (∀ p∈perturbClosed (0 : Space n) (1/2) 0, |h p| ≤ 1) →
      viscositySolution (perturbOpen (0 : Space n) (1/2) 0) (fun H _ => F H) (fun _ => 0) h →
      SchauderBound eta0 (backward (1/4)) h K ∧
      |h (0,0)| ≤ K ∧ ‖spatialD h (0,0)‖ ≤ K ∧ ‖hessian h (0,0)‖ ≤ K ∧
      |timeD (backward (1/4)) h (0,0)| ≤ K ∧
      timeD (backward (1/4)) h (0,0)=F (hessian h (0,0)) ∧
      ∀ r : ℝ, 0 < r → r ≤ 1/8 → ∀ p∈perturbClosed (0 : Space n) r 0,
        |h p-perturbPolynomial (h (0,0)) (spatialD h (0,0)) (hessian h (0,0))
          (timeD (backward (1/4)) h (0,0)) p| ≤ 3*K*r^(2+eta0) := by
  obtain ⟨eta, C, heta, heta1, hC, hRegular⟩ := hAuto n hn ell L hell hL
  let K : ℝ := 16 * (1 + (Fintype.card (RIdx n) : ℝ)) * (1 + C)
  have hd : 0 ≤ (Fintype.card (RIdx n) : ℝ) := Nat.cast_nonneg _
  have hK : 1 < K := by dsimp [K]; nlinarith [mul_nonneg hd hC.le]
  refine ⟨eta, K, heta, heta1, hK, ?_⟩
  intro F h hF hE hConc h0 hCont hSup hSol
  let G := perturbFrozenScale F
  let v : Point n → ℝ := fun p => h (perturbScale (1/2) p)
  have hG : Continuous G := by
    rw [show G = perturbOperatorScale F 0 4 from perturb_frozenScale_eq h0]
    exact perturb_operatorScale_continuous hF _ _
  have hGE : globalElliptic G ell L := by
    rw [show G = perturbOperatorScale F 0 4 from perturb_frozenScale_eq h0]
    exact perturb_operatorScale_elliptic hE (by norm_num) _
  have hGC : ConcaveOn ℝ univ G := by
    rw [show G = perturbOperatorScale F 0 4 from perturb_frozenScale_eq h0]
    exact perturb_operatorScale_concave hConc (by norm_num) _
  have hG0 : G 0 = 0 := by simp [G, perturbFrozenScale, h0]
  have hvCont : ContinuousOn v (unitClosed n) :=
    hCont.comp (perturbScale_continuous (1/2)).continuousOn (fun _ hp => perturb_half_scale_mem hp)
  have hvSup : ∀ p ∈ unitClosed n, |v p| ≤ 1 :=
    fun p hp => hSup _ (perturb_half_scale_mem hp)
  have hvSol : viscositySolution (unitOpen n) (fun H _ => G H) (fun _ => 0) v :=
    perturb_half_solution_to_unit hSol
  have hv := hRegular G hG hGE hGC hG0 v hvCont hvSup hvSol
  have hTransport := perturb_central_schauder_from_scaled heta1 hC hv
  have hSch : SchauderBound eta (backward (1/4)) h K := hTransport.2.1
  have hSubset : perturbOpen (0 : Space n) (1/4) 0 ⊆ perturbOpen (0 : Space n) (1/2) 0 := by
    intro p hp
    refine ⟨ball_subset_ball (by norm_num) hp.1, ?_, hp.2.2⟩
    have ht := hp.2.1
    norm_num at ht ⊢
    linarith
  have hNative : viscositySolution (perturbOpen (0 : Space n) (1/4) 0)
      (fun H _ => F H) (fun _ => 0) h :=
    ⟨fun p hp => hSol.1 p (hSubset hp), fun p hp => hSol.2 p (hSubset hp)⟩
  have hEquation := perturb_actual_equation_top (by norm_num : (0 : ℝ) < 1/4) hF hSch.1 hNative
  have hCoeff := hSch.2.2.1 (0, 0) perturb_quarter_origin
  have hTime : |timeD (backward (1/4)) h (0, 0)| ≤ K := by
    simpa only [Real.norm_eq_abs] using hSch.2.2.2.2.2.1 (0, 0) perturb_quarter_origin
  refine ⟨hSch, hCoeff.1, hCoeff.2, hTransport.2.2 (0, 0) perturb_quarter_origin,
    hTime, hEquation (0, 0) perturb_quarter_origin, ?_⟩
  intro r hr hrb p hp
  have hTaylor := perturb_taylor_remainder heta heta1 hSch hr hrb p hp
  change |h p - perturbTaylor (backward (1/4)) h (0 : Point n) p| ≤ 3 * K * r ^ (2 + eta) at hTaylor
  rw [perturb_taylor_origin_polynomial hSch.1 perturb_quarter_origin p] at hTaylor
  exact hTaylor

end Yau.LeafProofs.L05Aux
