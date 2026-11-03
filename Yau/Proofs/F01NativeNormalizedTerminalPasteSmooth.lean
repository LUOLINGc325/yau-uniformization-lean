import Yau.Proofs.F01NativeRestartPaste
import Yau.Proofs.F01NormalizedRestartClock
import Yau.Proofs.F01NativeClosedTerminalLeftData
import Yau.Proofs.F01ShiftedBackgroundJointSmooth
import Yau.Proofs.F01PotentialClosedFaceSmooth

/-! The actual original partial potential and the actual lifted restart
paste jointly smoothly in the same native normalized terminal charts.
All endpoint spatial jets are the constructed limits. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem native_normalized_terminal_paste_smooth
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (K : HermitianField M) (u : M.Carrier → ℝ) (hu : SmoothFn u)
    (hR : ℝ → HermitianField M) (W : M.Carrier → ℝ → ℝ)
    {σ Tstar ε r β : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius)
    (hEarly : 0 ≤ Tstar - σ ^ 2 / 4) (hr : 0 < r) (hrε : σ ^ 2 * r ≤ ε) (hβ : 0 < β)
    (hU : ∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Ico 0 Tstar, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ T, 0 ≤ T → T < Tstar → ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hTerminal : ∀ x, gMat K x = gMat g x - (Tstar : ℂ) • ricci g x + levi u x)
    (hW : SmoothSpaceTime W (Icc 0 ε)) (hW0 : ∀ x, W x 0 = u x)
    (hWpot : ∀ s ∈ Icc 0 ε, ∀ x,
      gMat (hR s) x = gMat g x - ((Tstar + s : ℝ) : ℂ) • ricci g x + levi (fun y => W y s) x)
    (hWPde : ∀ x s, s ∈ Icc 0 ε → HasDerivWithinAt (W x)
      (flowLogDetRatio g hR x s) (Icc 0 ε) s)
    (B : ℕ → ℝ)
    (hHolder : ∀ a k, HolderBound β (ball 0 (1 / 2) ×ˢ Ioo (Tstar - σ ^ 2 / 4) Tstar)
      (fun p => iteratedFDeriv ℝ k
        (fun z => (σ ^ 2)⁻¹ * U (A.chart a (σ • z)) p.2) p.1) (B k))
    (τ : ℕ → ℝ) (hτ : ∀ m, τ m ∈ Ioo (Tstar - σ ^ 2 / 4) Tstar)
    (hLim : Tendsto τ atTop (𝓝 Tstar))
    (hJets : ∀ a k, TendstoUniformlyOn
      (fun m x => iteratedFDeriv ℝ k
        (fun z => (σ ^ 2)⁻¹ * U (A.chart a (σ • z)) (τ m)) x)
      (iteratedFDeriv ℝ k (fun z => (σ ^ 2)⁻¹ * u (A.chart a (σ • z))))
      atTop (ball 0 (1 / 2))) :
    ∀ a, ContDiffOn ℝ ∞
      (shiftedNativePotential A (nativePastedRestartPotential U u W Tstar) a σ Tstar)
      (ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) r) := by
  intro a
  let F := shiftedNativePotential A (nativeClosedTerminalPotential U u Tstar) a σ Tstar
  let G := shiftedNativePotential A (absoluteRestartPotential W Tstar) a σ Tstar
  let S := shiftedComplexBackground A a σ Tstar
  let b : Point n → ℝ := fun p => normalizedPotentialLogSource A a σ p.1
  have hBall : ball (0 : Space n) (1 / 2) ⊆ ball 0 1 := ball_subset_ball (by norm_num)
  have hLeftData := native_closed_terminal_profile_left_data hg A h U K u hu hσ hσr hEarly
    hU hpot hpde hTerminal a
  have hPast : ContDiffOn ℝ ∞ (timeFacePaste F G 0)
      (ball 0 (1 / 2) ×ˢ Ioo (-(1 / 4 : ℝ)) r) := by
    apply potential_closed_face_paste_smooth F G b S isOpen_ball (by norm_num) hr
    · exact (shiftedComplexBackground_joint_smooth A hσ hσr Tstar a).mono
        (prod_mono hBall (subset_univ _))
    · exact (normalizedPotentialLogSource_smooth A hσ hσr a).comp contDiffOn_fst
        (fun p hp => hBall hp.1)
    · exact (native_closed_terminal_profile_smooth_left A U u hσ hσr hEarly hU a).mono
        (prod_mono hBall Subset.rfl)
    · exact (normalized_restart_profile_smooth A W hσ hσr hrε hW a Tstar).mono
        (prod_mono hBall Subset.rfl)
    · intro t ht
      exact (native_closed_terminal_profile_slices A U u hu hσ hσr hEarly hU a ht).mono hBall
    · intro k
      exact native_closed_terminal_profile_jet_continuity A U u a hσ hβ k
        (hHolder a k) τ hτ hLim (hJets a k)
    · intro x hx
      change shiftedNativePotential A (nativeClosedTerminalPotential U u Tstar) a σ Tstar (x, 0) =
        shiftedNativePotential A (absoluteRestartPotential W Tstar) a σ Tstar (x, 0)
      rw [native_closed_profile_at_zero, normalized_restart_profile_eq]
      simp only [mul_zero, hW0]
    · intro p hp
      exact (Complex.pos_iff.mp ((hLeftData.1 p ⟨hBall hp.1, hp.2⟩).det_pos)).1
    · intro p hp
      exact (Complex.pos_iff.mp ((normalized_restart_log_data hg A hR W hσ hσr hrε Tstar hW hWpot
        a (p := p) ⟨hBall hp.1, hp.2⟩).2.det_pos)).1
    · intro x hx t ht
      exact (hLeftData.2 x (hBall hx) t ht).hasDerivWithinAt
    · intro x hx t ht
      exact normalized_restart_clock_jet hg A hR W hσ hσr hrε Tstar hW hWpot hWPde a (hBall hx) ht
  exact hPast.congr (fun p hp => normalized_native_restart_paste A U u W a hσ Tstar p)

end Yau.NodeProofs.F01Aux
