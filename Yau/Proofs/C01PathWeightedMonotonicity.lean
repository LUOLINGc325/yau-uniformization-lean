import Yau.Proofs.C01PathHarnackInequality

/-! Integrating the actual scalar differential Harnack inequality
along the regularized clock, without a logarithm of scalar curvature. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

def scalarPathWeight {x₀ x₁ : Pt X} (h : Flow X) (γ : PiecewiseC1Curve x₀ x₁)
    (a b ε s : ℝ) : ℝ :=
  let v := curveSpeed (h a) γ
  let τ := regularizedTimeClock v a b ε
  τ s * scalarCurvature (h (τ s)) (γ s) * Real.exp (regularizedPathCost v a b ε s)

theorem localizedFlow_scalar_path_weight_monotoneOn
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    {x₀ x₁ : Pt X} (γ : PiecewiseC1Curve x₀ x₁) (a b ε : ℝ)
    (ha : 0 < a) (hab : a < b) (hε : 0 < ε)
    (hv : Continuous (curveSpeed (h a) γ))
    (hγc : ∀ s ∈ Set.Icc (0 : ℝ) 1, ContinuousAt γ.toFun s)
    (hγd : ∀ s ∈ Set.Icc (0 : ℝ) 1, DifferentiableAt ℝ
      (fun u : ℝ => extChartAt (ComplexModel n) (γ s) (γ u)) s) :
    MonotoneOn (scalarPathWeight h γ a b ε) (Set.Icc (0 : ℝ) 1) := by
  let v := curveSpeed (h a) γ
  let τ := regularizedTimeClock v a b ε
  let B := regularizedPathCost v a b ε
  have hprops := regularizedTimeClock_properties hv
    (fun s _ => Real.sqrt_nonneg _) a b ε hab hε
  have hd (s : ℝ) (hs : s ∈ Set.Icc (0 : ℝ) 1) :
      DifferentiableAt ℝ (scalarPathWeight h γ a b ε) s ∧
        0 ≤ deriv (scalarPathWeight h γ a b ε) s := by
    let α := (b - a) / (speedPrimitive v 1 + ε) * (v s + ε)
    let β := (speedPrimitive v 1 + ε) / (b - a) * v s
    let R := scalarCurvature (h (τ s)) (γ s)
    let Rₜ := deriv (fun t => scalarCurvature (h t) (γ s)) (τ s)
    let G := 2 * (∑ i, pathChartVelocity γ s i * wirt
      (fun z => Complex.ofReal (inChart (γ s) (scalarCurvature (h (τ s))) z))
        (chartPt (γ s) (γ s)) (stdVec i)).re
    have hτrange := hprops.1 hs
    have ht : 0 < τ s := ha.trans_le hτrange.1
    have hα : 0 < α := (hprops.2 s hs).1
    have hq : v s ^ 2 / 2 ≤ α * β := (hprops.2 s hs).2
    have hτ : HasDerivAt τ α s := regularizedTimeClock_hasDerivAt hv a b ε s
    have hB : HasDerivAt B β s := regularizedPathCost_hasDerivAt hv a b ε s
    have hR : HasDerivAt (fun u => scalarCurvature (h (τ u)) (γ u)) (G + α * Rₜ) s :=
      localizedFlow_scalar_along_path_hasDerivAt hflow γ τ s α (hγc s hs) (hγd s hs) hτ ht
    have hH := localizedFlow_path_speed_harnack hflow hjoint γ s a (τ s) α ha.le ht hτrange.1
    have hineq := scalar_clock_harnack_algebra R Rₜ G (v s ^ 2 / 2) (τ s) α β
      ht hα (localizedFlow_scalar_nonneg hflow (γ s) (τ s) ht.le) hH hq
    have hweight := scalar_integratingFactor_hasDerivAt hτ hR hB
    have hweight' : HasDerivAt (scalarPathWeight h γ a b ε)
        (Real.exp (B s) * (α * R + τ s * (G + α * Rₜ) + τ s * R * β)) s := hweight
    refine ⟨hweight'.differentiableAt, ?_⟩
    rw [hweight'.deriv]
    exact mul_nonneg (Real.exp_pos _).le hineq
  apply monotoneOn_of_deriv_nonneg (convex_Icc (0 : ℝ) 1)
    (fun s hs => (hd s hs).1.continuousAt.continuousWithinAt)
  · intro s hs
    exact (hd s (interior_subset hs)).1.differentiableWithinAt
  · intro s hs
    exact (hd s (interior_subset hs)).2

end Yau.NodeProofs.C01Aux
