import Yau.Proofs.F01TerminalRestartClock
import Yau.LeafProofs.L17

/-! The original proved short-time theorem is applied to the actual
constructed terminal field. Its new potential is computed relative
to the original background and original terminal clock. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau
variable {n : ℕ} {M : ComplexManifold n}

theorem exists_actual_lifted_terminal_restart
    (g K : HermitianField M) (hg : MetricSmooth g) (hK : MetricSmooth K)
    (hComplete : IsCompleteDistance (inducedDistance K))
    (hBG : Yau.LeafCandidates.HermitianBoundedGeometry K)
    (u : M.Carrier → ℝ) (hu : SmoothFn u) (T : ℝ)
    (hTerminal : ∀ x, gMat K x = gMat g x - (T : ℂ) • ricci g x + levi u x) :
    ∃ ε D : ℝ, 0 < ε ∧ 1 ≤ D ∧
      ∃ (h : ℝ → HermitianField M) (W : M.Carrier → ℝ → ℝ),
        h 0 = K ∧ MetricFamilySmooth h (Icc 0 ε) ∧ SmoothSpaceTime W (Icc 0 ε) ∧
        (∀ x, W x 0 = u x) ∧
        ∀ x s, s ∈ Icc 0 ε →
          (gMat (h s) x - ((D⁻¹ : ℝ) : ℂ) • gMat K x).PosSemidef ∧
          ((D : ℂ) • gMat K x - gMat (h s) x).PosSemidef ∧
          gMat (h s) x = gMat g x - ((T + s : ℝ) : ℂ) • ricci g x + levi (fun y => W y s) x ∧
          HasDerivWithinAt (W x) (flowLogDetRatio g h x s) (Icc 0 ε) s := by
  obtain ⟨ε, D, hε, hD, h, V, h0, hh, hV, hV0, hData⟩ :=
    Yau.LeafProofs.L17 n M K hK hComplete hBG
  let W := liftedRestartPotential g K u V
  have hPDE : ∀ x s, s ∈ Icc 0 ε → HasDerivWithinAt (V x)
      (flowLogDetRatio K h x s) (Icc 0 ε) s := fun x s hs => (hData x s hs).2.2.2
  refine ⟨ε, D, hε, hD, h, W, h0, hh, liftedRestartPotential_smooth g K hg hK u hu V hV,
    (fun x => liftedRestartPotential_initial g K u V hV0 x), ?_⟩
  intro x s hs
  have hIdentity := lifted_restart_metric_potential_identity g K hg hK u hu h V T s
    (smoothSpaceTime_slice hV hs) hTerminal (fun y => (hData y s hs).2.2.1)
  exact ⟨(hData x s hs).1, (hData x s hs).2.1, hIdentity x,
    lifted_restart_time_equation g K u h V h0 hPDE x s hs⟩

end Yau.NodeProofs.F01Aux
