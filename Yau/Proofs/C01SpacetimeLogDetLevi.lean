import Yau.Proofs.C01SpacetimeCurvature
import Yau.Proofs.C01LogDetMixedTrace
import Yau.Proofs.C01TraceQuadraticAlgebra

/-! Taking the actual metric trace of the computed joint curvature gives
the Levi inequality for the original negative log determinant. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]

theorem wirt_neg_fn (f : V → ℂ) (z v : V) :
    wirt (fun p => -f p) z v = -wirt f z v := by
  unfold wirt
  rw [fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]
  ring

theorem wirtBar_neg_fn (f : V → ℂ) (z v : V) :
    wirtBar (fun p => -f p) z v = -wirtBar f z v := by
  unfold wirtBar
  rw [fderiv_fun_neg]
  simp only [ContinuousLinearMap.neg_apply]
  ring

theorem mixedLevi_neg_fn (f : V → ℂ) (z v w : V) :
    wirt (fun p => wirtBar (fun q => -f q) p v) z w =
      -(wirt (fun p => wirtBar f p v) z w) := by
  have hinner : (fun p => wirtBar (fun q => -f q) p v) =
      (fun p => -wirtBar f p v) := funext fun p => wirtBar_neg_fn f p v
  rw [hinner, wirt_neg_fn]

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

theorem localizedFlow_spacetime_negativeLogDet_levi_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (z d : ComplexVector n) (hz : z ∈ chartTarget x) (w τ : ℂ) :
    let H := spacetimeMetricLine h x z d w τ
    0 ≤ (wirt (fun p => wirtBar (fun q : ℂ =>
      ((-Real.log (H q).det.re : ℝ) : ℂ)) p 1) 0 1).re := by
  dsimp only
  let H := spacetimeMetricLine h x z d w τ
  let S : Set ℂ := {ζ | z + ζ • d ∈ chartTarget x}
  have hS : IsOpen S :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).preimage (by fun_prop)
  have hzero : (0 : ℂ) ∈ S := by simpa only [S, Set.mem_setOf_eq, zero_smul, add_zero] using hz
  have hlinear : ContDiff ℝ ∞ (fun ζ : ℂ => w + ζ * τ) := by fun_prop
  have hclock : ContDiff ℝ ∞ (fun ζ : ℂ => Real.exp (2 * (w + ζ * τ).re)) :=
    (contDiff_const.mul (Complex.reCLM.contDiff.comp hlinear)).exp
  have hmap : ContDiffOn ℝ ∞
      (fun ζ : ℂ => (z + ζ • d, Real.exp (2 * (w + ζ * τ).re))) S :=
    (show ContDiff ℝ ∞ (fun ζ : ℂ => z + ζ • d) from by fun_prop).contDiffOn.prodMk
      hclock.contDiffOn
  have hH (i j : Fin n) : ContDiffOn ℝ ∞ (fun ζ : ℂ => H ζ i j) S :=
    (Alignment.Y03Proof.metricFamily_hMat_contDiffOn hflow.1.2.1 x i j).comp hmap
      (fun ζ hζ => ⟨hζ, (Real.exp_pos _).le⟩)
  have hpos (ζ : ℂ) (hζ : ζ ∈ S) : (H ζ).PosDef :=
    Alignment.Y03Proof.hMat_posDef _ x _ hζ
  have hcurv := localizedFlow_spacetime_curvature_nonneg hflow hjoint x z d hz w τ
  have htrace := matrix_logDet_mixed_trace H S hS hH hpos 0 1 1 hzero
  simp only [Complex.ofReal_neg]
  rw [mixedLevi_neg_fn, htrace]
  exact trace_mul_nonneg_of_real_quadratics _ _ (hpos 0 hzero).inv.posSemidef hcurv

end Yau.NodeProofs.C01Aux
