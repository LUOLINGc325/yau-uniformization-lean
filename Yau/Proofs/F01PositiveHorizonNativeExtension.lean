import Yau.Proofs.F01ActualLongerNativeSolution
import Yau.Proofs.F01TerminalScaleChoice

/-! Every actual uniformly comparable partial native potential solution
at a positive finite horizon extends to a strictly longer closed interval.
The backward scale is constructed inside the given true chart radius. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_native_extension_of_positive_horizon
    (g : HermitianField M) (hg : MetricSmooth g) (A : BoundedChartFamily g)
    {T C : ℝ} (hT : 0 < T) (hC : 1 ≤ C)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (hU : ∀ s, 0 ≤ s → s < T → SmoothSpaceTime U (Icc 0 s))
    (hU0 : ∀ x, U x 0 = 0)
    (hpot : ∀ s ∈ Ico 0 T, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ s, 0 ≤ s → s < T → ∀ x t, t ∈ Icc 0 s →
      HasDerivWithinAt (U x) (flowLogDetRatio g h x t) (Icc 0 s) t)
    (hflow : ∀ x t, t ∈ Ico 0 T →
      (gMat (h t) x - ((C⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
      ((C : ℂ) • gMat g x - gMat (h t) x).PosSemidef) :
    ∃ (Tnew Cnew : ℝ) (hNew : ℝ → HermitianField M) (V : M.Carrier → ℝ → ℝ),
      T < Tnew ∧ 1 ≤ Cnew ∧ hNew 0 = h 0 ∧ (∀ x, V x 0 = 0) ∧
      (∀ s, s < T → hNew s = h s ∧ ∀ x, V x s = U x s) ∧
      MetricFamilySmooth hNew (Icc 0 Tnew) ∧ SmoothSpaceTime V (Icc 0 Tnew) ∧
      ∀ x t, t ∈ Icc 0 Tnew →
        (gMat (hNew t) x - ((Cnew⁻¹ : ℝ) : ℂ) • gMat g x).PosSemidef ∧
        ((Cnew : ℂ) • gMat g x - gMat (hNew t) x).PosSemidef ∧
        gMat (hNew t) x = gMat g x - (t : ℂ) • ricci g x + levi (fun y => V y t) x ∧
        HasDerivWithinAt (V x) (flowLogDetRatio g hNew x t) (Icc 0 Tnew) t := by
  obtain ⟨ρ, hρ, hρr, hρ1, hEarly⟩ := exists_native_terminal_scale A.radius_pos hT
  exact exists_actual_longer_native_solution g hg A hρ hρr hρ1 hT.le hC hEarly
    h U hU hU0 hpot hpde hflow

end Yau.NodeProofs.F01Aux
