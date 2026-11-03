import Yau.Proofs.F01BackwardNativeChuInputs
import Yau.Proofs.F01LogDetInteriorSchauder
import Yau.Proofs.F01BackwardSchauderRestriction

/-! Actual positive-time Schauder estimates up to the supplied final
flow time. All native Chu inputs are constructed and no future-time
buffer, solver, or full-Hessian premise is introduced. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem backward_native_schauder
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tcap C α β : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTcap : 0 ≤ Tcap) (hC : 1 ≤ C) (hα : 0 < α) (hα1 : α < 1) (hβ : 0 < β) (hβ1 : β < 1) :
    ∃ K : ℝ, 0 < K ∧
      ∀ (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ) (T τ : ℝ),
      T ≤ Tcap → ρ ^ 2 ≤ τ → τ ≤ T →
      SmoothSpaceTime U (Icc 0 T) → (∀ x, U x 0 = 0) →
      (∀ s ∈ Icc 0 T, ∀ x,
        gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x) →
      (∀ x s, s ∈ Icc 0 T → HasDerivWithinAt (U x)
        (flowLogDetRatio g h x s) (Icc 0 T) s) →
      (∀ x s, s ∈ Icc 0 T →
        (gMat (h s) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((C : ℂ) • gMat g x - gMat (h s) x).PosSemidef) → ∀ a : M.Carrier,
      SchauderBound (min α β) (cylinder (ball 0 (1 / 2)) (-(1 / 8)) 0)
        (shiftedNativePotential A U a ρ τ) K := by
  obtain ⟨ell, upper, K0, B, hell, hUpper, hK0, hB, hInputs⟩ :=
    exists_shifted_backward_native_chu_inputs g hg A hρ hρr hρ1 hTcap hC hα1.le hβ1.le
  obtain ⟨K, hK, hEstimate⟩ := native_logdet_backward_schauder
    (Yau.LeafProofs.L12Aux.manifold_dimension_pos M) hα hα1 hβ hβ1 hell hUpper hK0 hB
  refine ⟨K, hK, ?_⟩
  intro h U T τ hCap hLower hUpperTime hU hU0 hpot hpde hflow a
  obtain ⟨hS, hf, hu, hSup, hRange, hEquation⟩ :=
    hInputs h U T τ hCap hLower hUpperTime hU hU0 hpot hpde hflow a
  have hSub : backward (n := n) 1 ⊆ cylinder (ball 0 1) (-1) 0 := by
    intro p hp
    exact ⟨hp.1, by simpa only [one_pow] using hp.2.1.le, hp.2.2⟩
  have hC2 : C2 (backward 1) (shiftedNativePotential A U a ρ τ) := by
    simpa only [backward, one_pow] using c2_closed_open_lower hu
  have hEq : ∀ p ∈ backward 1,
      timeD (backward 1) (shiftedNativePotential A U a ρ τ) p -
        logDetReal (iota (shiftedComplexBackground A a ρ τ p) +
          complexHessianMap (hessian (shiftedNativePotential A U a ρ τ) p)) =
        normalizedPotentialLogSource A a ρ p.1 := by
    intro p hp
    have hOpen : p ∈ ball (0 : Space n) 1 ×ˢ Ioc (-1) 0 := by
      simpa only [backward, one_pow] using hp
    have ht := timeD_closed_open_lower (shiftedNativePotential A U a ρ τ) hOpen
    have hh := hEquation p (hSub hp)
    simpa only [backward, one_pow, ht] using hh
  have hSch := hEstimate (fun p => iota (shiftedComplexBackground A a ρ τ p))
    (fun p => normalizedPotentialLogSource A a ρ p.1) (shiftedNativePotential A U a ρ τ)
    (holderBound_restrict hS hSub) (holderBound_restrict hf hSub) hC2
    (fun p hp => hSup p (hSub hp)) (fun p hp => hRange p (hSub hp)) hEq
  apply backward_schauder_closed_restrict hu hSch Subset.rfl (ball_subset_ball (by norm_num : (1 / 2 : ℝ) ≤ 1))
  · intro t ht
    constructor <;> nlinarith [ht.1, ht.2]
  · intro t ht
    exact ⟨by nlinarith [ht.1], ht.2⟩
  · norm_num

end Yau.NodeProofs.F01Aux
