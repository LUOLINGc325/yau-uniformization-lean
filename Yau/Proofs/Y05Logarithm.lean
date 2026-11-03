import Yau.Geometry.Basic
import Mathlib.Analysis.Complex.BranchLogRoot
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Calculus.FDeriv.OfCompLeft
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

noncomputable section
open Filter Set
open scoped Topology

namespace Yau.Proofs.Y05Aux

open Yau

variable {n : ℕ}

/-- A continuous branch of a nonvanishing holomorphic exponential is itself holomorphic. -/
theorem differentiableOn_exp_lift {O : Set (ComplexVector n)} (hO : IsOpen O)
    {g L : ComplexVector n → ℂ} (hg : DifferentiableOn ℂ g O)
    (hL : ContinuousOn L O) (hExp : ∀ z ∈ O, Complex.exp (L z) = g z) :
    DifferentiableOn ℂ L O := by
  intro z hz
  have hLc : ContinuousAt L z := hL.continuousAt (hO.mem_nhds hz)
  have hg' := ((hg z hz).differentiableAt (hO.mem_nhds hz)).hasFDerivAt
  let D : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (L z))
  let K : ℂ →L[ℂ] ℂ := ContinuousLinearMap.toSpanSingleton ℂ (Complex.exp (L z))⁻¹
  have hD : HasFDerivAt Complex.exp D (L z) := by
    convert (Complex.hasDerivAt_exp (L z)).hasFDerivAt using 1
  have hInv : Function.LeftInverse K D := by
    intro w
    simp [K, D, Complex.exp_ne_zero]
  have hEq : Complex.exp ∘ L =ᶠ[𝓝 z] g := by
    filter_upwards [hO.mem_nhds hz] with w hw
    exact hExp w hw
  exact (HasFDerivAt.of_comp_of_leftInverse hLc hD hg' hEq hInv).differentiableAt.differentiableWithinAt

/-- The branch is normalized at zero on one fixed ball; no branch solver is an input. -/
theorem exists_normalized_holomorphic_log {r : ℝ} (hr : 0 < r)
    {g : ComplexVector n → ℂ} (hg : DifferentiableOn ℂ g (Metric.ball 0 r))
    (hzero : g 0 = 1) (hne : ∀ z ∈ Metric.ball (0 : ComplexVector n) r, g z ≠ 0) :
    ∃ P : ComplexVector n → ℂ,
      P 0 = 0 ∧ DifferentiableOn ℂ P (Metric.ball 0 r) ∧
      ∀ z ∈ Metric.ball (0 : ComplexVector n) r, Complex.exp (P z) = g z := by
  haveI : ContractibleSpace (Metric.ball (0 : ComplexVector n) r) :=
    (convex_ball (0 : ComplexVector n) r).contractibleSpace ⟨0, Metric.mem_ball_self hr⟩
  have hsc : IsSimplyConnected (Metric.ball (0 : ComplexVector n) r) := by
    change SimplyConnectedSpace (Metric.ball (0 : ComplexVector n) r)
    infer_instance
  obtain ⟨L, hL, hExp⟩ := Complex.exists_continuousOn_eqOn_exp_comp hsc Metric.isOpen_ball
    hg.continuousOn (by
      rintro ⟨z, hz, heq⟩
      exact hne z hz heq)
  have hdL : DifferentiableOn ℂ L (Metric.ball 0 r) :=
    differentiableOn_exp_lift Metric.isOpen_ball hg hL (fun z hz => hExp hz)
  have hL0 : Complex.exp (L 0) = 1 := (hExp (Metric.mem_ball_self hr)).trans hzero
  refine ⟨fun z => L z - L 0, sub_self _, hdL.sub_const _, ?_⟩
  intro z hz
  rw [Complex.exp_sub, hL0, div_one]
  exact hExp hz

end Yau.Proofs.Y05Aux
