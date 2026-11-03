import Yau.Proofs.F01BackwardNativeEquation
import Yau.Proofs.F01ShiftedPotentialSup
import Yau.Proofs.F01NativeChartSandwich
import Yau.Proofs.F01InteriorSchauderTransfer

/-! Original Chu inputs on a backward patch ending at the actual
flow time. All budgets precede the realized flow and clock center;
no future-time buffer or second-derivative oracle is assumed. -/
noncomputable section
open Set Metric
open scoped ContDiff Manifold Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

def NativeLogDetBackwardInputs (α β ell upper K B : ℝ)
    (S : Point n → Sym n) (f u : Point n → ℝ) : Prop :=
  let Q := cylinder (ball (0 : Space n) 1) (-1) 0
  HolderBound β Q S K ∧ HolderBound α Q f K ∧ C2 Q u ∧
    (∀ p ∈ Q, |u p| ≤ B) ∧
    (∀ p ∈ Q, (((S p + complexHessianMap (hessian u p) : Sym n) : Mat n) - ell • 1).PosSemidef ∧
      (upper • 1 - ((S p + complexHessianMap (hessian u p) : Sym n) : Mat n)).PosSemidef) ∧
    ∀ p ∈ Q, timeD Q u p - logDetReal (S p + complexHessianMap (hessian u p)) = f p

theorem exists_shifted_backward_native_chu_inputs
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {ρ Tcap C α β : ℝ} (hρ : 0 < ρ) (hρr : ρ ≤ A.radius) (hρ1 : ρ ≤ 1)
    (hTcap : 0 ≤ Tcap) (hC : 1 ≤ C) (hα : α ≤ 1) (hβ : β ≤ 1) :
    ∃ ell upper K B : ℝ, 0 < ell ∧ ell ≤ upper ∧ 0 < K ∧ 0 ≤ B ∧
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
      NativeLogDetBackwardInputs α β ell upper K B
        (fun p => iota (shiftedComplexBackground A a ρ τ p))
        (fun p => normalizedPotentialLogSource A a ρ p.1) (shiftedNativePotential A U a ρ τ) := by
  obtain ⟨D, hD, hMetric⟩ := dilated_native_metric_sandwich A hC
  have hDp : 0 < D := zero_lt_one.trans_le hD
  have hInv : D⁻¹ ≤ D :=
    ((inv_le_one₀ hDp).mpr hD).trans hD
  obtain ⟨Ks, hKs, hS⟩ := shifted_real_background_holder_budget A hTcap hβ
  obtain ⟨Kd, hKd, hd⟩ := normalizedPotentialLogSource_spatial_holder_budgets A hα
  let K := max Ks (Kd 0)
  let B := (ρ ^ 2)⁻¹ * (((n : ℝ) * Real.log C) * Tcap)
  have hB : 0 ≤ B := mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg _) (Real.log_nonneg hC)) hTcap)
  refine ⟨D⁻¹, D, K, B, inv_pos.mpr hDp, hInv, hKs.trans_le (le_max_left _ _), hB, ?_⟩
  intro h U T τ hCap hLower hUpper hU hU0 hpot hpde hflow a
  dsimp only [NativeLogDetBackwardInputs]
  have hτ : |τ| ≤ Tcap := by
    rw [abs_of_nonneg (by nlinarith [sq_nonneg ρ] : 0 ≤ τ)]
    nlinarith [sq_nonneg ρ]
  have hEquation := shifted_backward_native_real_equation hg A h U hρ hρr hLower hUpper hU hpot hpde a
  have hf := holderBound_from_zero_spatial_jet (n := n) (F := ℝ)
    (f := fun p : Point n => normalizedPotentialLogSource A a ρ p.1) (hd 0 ρ hρ hρr hρ1 a)
  have hSub : cylinder (ball (0 : Space n) 1) (-1) 0 ⊆ cylinder (ball 0 1) (-1) 1 :=
    fun p hp => ⟨hp.1, hp.2.1, hp.2.2.trans zero_le_one⟩
  refine ⟨holderBound_mono_const (holderBound_restrict (hS ρ τ hρ hρr hρ1 hτ a) hSub) (le_max_left _ _),
    holderBound_mono_const (holderBound_restrict hf hSub) (le_max_right _ _), hEquation.1,
    shifted_backward_native_potential_sup g A h U hC hLower hUpper hCap hU0 hpde hflow a, ?_, hEquation.2⟩
  intro p hp
  rw [real_chart_potential_matrix hEquation.1 hp,
    shifted_native_flow_matrix_at hg A h U hρ.ne' hU hpot a p
      (spatialDilation_mem_ball hρ hρr hp.1) (shifted_backward_clock_maps hLower hUpper hp.2)]
  have ht := shifted_backward_clock_maps hLower hUpper hp.2
  have hh := hMetric (h (affineParabolicPoint ρ 0 τ p).2) ρ hρ hρr
    (fun x => hflow x _ ht) a p.1 hp.1
  simpa only [affineParabolicPoint, add_zero] using iota_scalar_matrix_sandwich hh.1 hh.2

end Yau.NodeProofs.F01Aux
