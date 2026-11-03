import Yau.Proofs.F01NativeClosedProfileIdentity
import Yau.Proofs.F01PartialTerminalClockEquation
import Yau.Proofs.F01NormalizedNativeSliceMatrix

/-! The explicitly closed partial potential has an actually positive
matrix on its closed terminal face and its original clock equation
on the open left side. -/
noncomputable section
open Set Filter Metric
open scoped ContDiff Topology Matrix ComplexOrder Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem native_closed_terminal_profile_left_data
    (hg : MetricSmooth g) (A : BoundedChartFamily g)
    (h : ℝ → HermitianField M) (U : M.Carrier → ℝ → ℝ)
    (K : HermitianField M) (u : M.Carrier → ℝ) (hu : SmoothFn u)
    {σ Tstar : ℝ} (hσ : 0 < σ) (hσr : σ ≤ A.radius)
    (hEarly : 0 ≤ Tstar - σ ^ 2 / 4)
    (hU : ∀ T, 0 ≤ T → T < Tstar → SmoothSpaceTime U (Icc 0 T))
    (hpot : ∀ s ∈ Ico 0 Tstar, ∀ x,
      gMat (h s) x = gMat g x - (s : ℂ) • ricci g x + levi (fun y => U y s) x)
    (hpde : ∀ T, 0 ≤ T → T < Tstar → ∀ x s, s ∈ Icc 0 T →
      HasDerivWithinAt (U x) (flowLogDetRatio g h x s) (Icc 0 T) s)
    (hTerminal : ∀ x, gMat K x = gMat g x - (Tstar : ℂ) • ricci g x + levi u x)
    (a : M.Carrier) :
    let F := shiftedNativePotential A (nativeClosedTerminalPotential U u Tstar) a σ Tstar
    let S := shiftedComplexBackground A a σ Tstar
    (∀ p ∈ ball 0 1 ×ˢ Ioc (-(1 / 4 : ℝ)) 0, (chartPotentialMatrix S F p).PosDef) ∧
    ∀ x ∈ ball 0 1, ∀ t ∈ Ioo (-(1 / 4 : ℝ)) 0,
      HasDerivAt (fun s => F (x, s))
        (localPotentialClockRHS S (fun p => normalizedPotentialLogSource A a σ p.1) F (x, t)) t := by
  let F := shiftedNativePotential A (nativeClosedTerminalPotential U u Tstar) a σ Tstar
  let F0 := shiftedNativePotential A U a σ Tstar
  let S := shiftedComplexBackground A a σ Tstar
  have hEq (x : Space n) {t : ℝ} (ht : t < 0) :
      (fun z => F (z, t)) = (fun z => F0 (z, t)) := by
    funext z
    exact native_closed_profile_eq_on_negative_clock A U u a hσ Tstar ht
  constructor
  · rintro ⟨x, t⟩ hp
    by_cases he : t = 0
    · subst t
      have hSlice : (fun z => F (z, 0)) =
          (fun z => (σ ^ 2)⁻¹ * u (A.chart a (σ • z))) :=
        funext (fun z => native_closed_profile_at_zero A U u a σ Tstar z)
      have hMatrix : chartPotentialMatrix S F (x, 0) = pullbackMatrix K (A.chart a) (σ • x) := by
        change S (x, 0) + leviC (fun z => F (z, 0)) x = _
        rw [hSlice]
        exact normalized_native_slice_matrix_at hg A K u hu hσ.ne' a (x, 0)
          (spatialDilation_mem_ball hσ hσr hp.1)
          (by simpa only [mul_zero, add_zero] using hTerminal)
      rw [hMatrix]
      exact pullbackMatrix_posDef K (A.chart a) (A.differentiable a) (A.inverse_differentiable a)
        (A.closedBall_source a (ball_subset_closedBall (spatialDilation_mem_ball hσ hσr hp.1)))
    · have ht : t < 0 := lt_of_le_of_ne hp.2.2 he
      change (S (x, t) + leviC (fun z => F (z, t)) x).PosDef
      rw [hEq x ht]
      exact (partial_terminal_shifted_clock_jet hg A h U hσ hσr hEarly hU hpot hpde a hp.1
        ⟨hp.2.1, ht⟩).2
  · intro x hx t ht
    have hOld := (partial_terminal_shifted_clock_jet hg A h U hσ hσr hEarly hU hpot hpde a hx ht).1
    have hCurve : (fun s => F (x, s)) =ᶠ[𝓝 t] (fun s => F0 (x, s)) := by
      filter_upwards [Iio_mem_nhds ht.2] with s hs
      exact native_closed_profile_eq_on_negative_clock A U u a hσ Tstar hs
    have hh := hOld.congr_of_eventuallyEq hCurve
    have hRHS : localPotentialClockRHS S (fun p => normalizedPotentialLogSource A a σ p.1) F (x, t) =
        localPotentialClockRHS S (fun p => normalizedPotentialLogSource A a σ p.1) F0 (x, t) := by
      unfold localPotentialClockRHS
      rw [hEq x ht.2]
    exact hh.congr_deriv hRHS.symm

end Yau.NodeProofs.F01Aux
