import Yau.Proofs.C01ClockTimeJets

/-! The actual spatial/time Levi cross term is t times the spatial
Wirtinger derivative of the same original scalar curvature. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

theorem product_spatial_wirt
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : E × ℂ → ℂ} (z d : E) (w : ℂ) (hF : DifferentiableAt ℝ F (z, w)) :
    wirt (fun p => F (p, w)) z d = wirt F (z, w) (d, 0) := by
  let γ : E → E × ℂ := fun p => (p, w)
  have hγd : HasFDerivAt γ ((ContinuousLinearMap.id ℂ E).prod 0) z := by
    simpa only [id_eq] using! (hasFDerivAt_id z).prodMk (hasFDerivAt_const w z)
  have hc := wirt_comp_holomorphic (f := F) (γ := γ) (v := d) hF hγd.differentiableAt
  rw [hγd.fderiv] at hc
  simpa only [γ, Function.comp_def, ContinuousLinearMap.prod_apply,
    ContinuousLinearMap.id_apply, ContinuousLinearMap.zero_apply] using hc

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem negativeLogDetClock_mixed_cross
    (hflow : LocalizedFlow X o h U P ρ) (x : Pt X)
    (z d : ComplexVector n) (hz : z ∈ chartTarget x) (w : ℂ) :
    let t := Real.exp (2 * w.re)
    wirt (fun p => wirtBar (fun q : ComplexVector n × ℂ =>
      (negativeLogDetClock h x q : ℂ)) p (0, 1)) (z, w) (d, 0) =
      (t : ℂ) * wirt (fun u => (scalarCurvature (h t) (chartInv x u) : ℂ)) z d := by
  dsimp only
  let t := Real.exp (2 * w.re)
  let F : ComplexVector n × ℂ → ℂ := fun p => (negativeLogDetClock h x p : ℂ)
  let B : ComplexVector n → ℂ := fun u => wirtBar F (u, w) (0, 1)
  let R : ComplexVector n → ℂ := fun u => (scalarCurvature (h t) (chartInv x u) : ℂ)
  have hF : ContDiffAt ℝ 2 F (z, w) :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp _
      ((negativeLogDetClock_contDiffAt hflow x (z, w) hz).of_le (by simp))
  have hbar : DifferentiableAt ℝ (fun p => wirtBar F p (0, 1)) (z, w) :=
    (wirtBar_contDiffAt hF (0, 1)).differentiableAt (by norm_num)
  have hBd : DifferentiableAt ℝ B z := by
    simpa only [B, Function.comp_def] using!
      hbar.comp z (show DifferentiableAt ℝ (fun u : ComplexVector n => (u, w)) z from by fun_prop)
  have hBgerm : B =ᶠ[𝓝 z] (fun u => (t : ℂ) * R u) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with u hu
    exact negativeLogDetClock_wirtBar_time hflow x u hu w
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (Real.exp_pos _).ne'
  have hRgerm : R =ᶠ[𝓝 z] (fun u => (t : ℂ)⁻¹ * B u) := by
    filter_upwards [hBgerm] with u hu
    rw [hu, ← mul_assoc, inv_mul_cancel₀ htC, one_mul]
  have hRd : DifferentiableAt ℝ R z :=
    (hBd.const_mul ((t : ℂ)⁻¹)).congr_of_eventuallyEq hRgerm
  have hc := product_spatial_wirt z d w hbar
  change wirt (fun p => wirtBar F p (0, 1)) (z, w) (d, 0) = (t : ℂ) * wirt R z d
  rw [← hc, wirt_congr_germ hBgerm d]
  exact wirt_const_mul_fn hRd d (t : ℂ)

end Yau.NodeProofs.C01Aux
