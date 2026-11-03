import Yau.Proofs.F01TerminalClockClosure

/-! The explicit native potential obtained by assigning its constructed
terminal value at the terminal clock. Its normalized profiles are the
same closed-face profiles used in the actual jet-limit theorem. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def nativeClosedTerminalPotential (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    (T : ℝ) (x : M.Carrier) (t : ℝ) : ℝ := if t = T then u x else U x t

theorem native_closed_terminal_profile_eq
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    (a : M.Carrier) (σ T : ℝ) (p : Point n) :
    shiftedNativePotential A (nativeClosedTerminalPotential U u T) a σ T p =
      closeTerminalTimeFace
        (fun q => (σ ^ 2)⁻¹ * U (A.chart a (σ • q.1)) q.2)
        (fun z => (σ ^ 2)⁻¹ * u (A.chart a (σ • z))) T (p.1, T + σ ^ 2 * p.2) := by
  by_cases he : T + σ ^ 2 * p.2 = T
  · simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
      affineParabolicPoint, nativeClosedTerminalPotential, closeTerminalTimeFace, add_zero, he,
      ite_true]
  · simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
      affineParabolicPoint, nativeClosedTerminalPotential, closeTerminalTimeFace, add_zero,
      if_neg he]

theorem native_closed_terminal_profile_smooth_left
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    {σ T : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius)
    (hEarly : 0 ≤ T - σ ^ 2 / 4)
    (hU : ∀ s, 0 ≤ s → s < T → SmoothSpaceTime U (Icc 0 s)) (a : M.Carrier) :
    ContDiffOn ℝ ∞ (shiftedNativePotential A (nativeClosedTerminalPotential U u T) a σ T)
      (ball 0 1 ×ˢ Ioo (-(1 / 4 : ℝ)) 0) := by
  have hf : ContDiffOn ℝ ∞
      (fun p : Point n => (σ ^ 2)⁻¹ * U (A.chart a (σ • p.1)) (T + σ ^ 2 * p.2))
      (ball 0 1 ×ˢ Ioo (-(1 / 4 : ℝ)) 0) := by
    apply (partial_terminal_shifted_potential_smooth A U hσ hσr hEarly hU a).congr
    intro p hp
    simp only [shiftedNativePotential, affineParabolicPotential, affineParabolicPullback,
      affineParabolicPoint, add_zero]
  have hh := close_terminal_face_smooth_on_open_left
    (fun q : Point n => (σ ^ 2)⁻¹ * U (A.chart a (σ • q.1)) q.2)
    (fun z => (σ ^ 2)⁻¹ * u (A.chart a (σ • z))) (sq_pos_of_pos hσ) T hf
  exact hh.congr (fun p hp => native_closed_terminal_profile_eq A U u a σ T p)

theorem native_closed_terminal_profile_jet_continuity
    (A : BoundedChartFamily g) (U : M.Carrier → ℝ → ℝ) (u : M.Carrier → ℝ)
    (a : M.Carrier) {σ T β C : ℝ} (hσ : 0 < σ) (hβ : 0 < β) (k : ℕ)
    (hf : HolderBound β (ball 0 (1 / 2) ×ˢ Ioo (T - σ ^ 2 / 4) T)
      (fun p => iteratedFDeriv ℝ k
        (fun z => (σ ^ 2)⁻¹ * U (A.chart a (σ • z)) p.2) p.1) C)
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ Ioo (T - σ ^ 2 / 4) T)
    (hLim : Tendsto τ atTop (𝓝 T))
    (hJets : TendstoUniformlyOn
      (fun m x => iteratedFDeriv ℝ k
        (fun z => (σ ^ 2)⁻¹ * U (A.chart a (σ • z)) (τ m)) x)
      (iteratedFDeriv ℝ k (fun z => (σ ^ 2)⁻¹ * u (A.chart a (σ • z))))
      atTop (ball 0 (1 / 2))) :
    ContinuousOn (fun p : Point n => iteratedFDeriv ℝ k
      (fun z => shiftedNativePotential A (nativeClosedTerminalPotential U u T) a σ T (z, p.2)) p.1)
      (ball 0 (1 / 2) ×ˢ Ioc (-(1 / 4 : ℝ)) 0) := by
  have hh := normalized_closed_terminal_spatial_jet_continuity (ball 0 (1 / 2))
    (fun q : Point n => (σ ^ 2)⁻¹ * U (A.chart a (σ • q.1)) q.2)
    (fun z => (σ ^ 2)⁻¹ * u (A.chart a (σ • z)))
    (sq_pos_of_pos hσ) hβ k hf τ hτ hLim hJets
  apply hh.congr
  intro p hp
  exact congrArg (fun q : Space n → ℝ => iteratedFDeriv ℝ k q p.1)
    (funext (fun z => native_closed_terminal_profile_eq A U u a σ T (z, p.2)))

end Yau.NodeProofs.F01Aux
