import Yau.Proofs.C01JointDirections
import Yau.Proofs.C01CometricCurvature

/-! The generic cometric calculation applied to precisely the metric,
spatial chart, and logarithmic time of the original localized flow. -/

noncomputable section

open scoped Manifold Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint

variable {n : ℕ} {X : KahlerManifold n} {o : Pt X}
  {h : Flow X} {U P ρ : STF X}

def spacetimeMetricLine (h : Flow X) (x : Pt X)
    (z d : ComplexVector n) (w τ ζ : ℂ) : Herm n :=
  hMat (h (Real.exp (2 * (w + ζ * τ).re))) x (z + ζ • d)

theorem localizedFlow_spacetime_curvature_nonneg
    (hflow : LocalizedFlow X o h U P ρ) (hjoint : JointPositivity X h)
    (x : Pt X) (z d : ComplexVector n) (hz : z ∈ chartTarget x) (w τ : ℂ) :
    let H := spacetimeMetricLine h x z d w τ
    let H₁ : Herm n := fun i j => wirt (fun p => H p i j) 0 1
    let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) 0 1
    let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p 1) 0 1
    ∀ v : Fin n → ℂ,
      0 ≤ (star v ⬝ᵥ ((-H₁₂ + H₂ * (H 0)⁻¹ * H₁) *ᵥ v)).re := by
  let S : Set ℂ := {ζ | z + ζ • d ∈ chartTarget x}
  have hS : IsOpen S :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).preimage (by fun_prop)
  have hzero : (0 : ℂ) ∈ S := by simpa only [S, Set.mem_setOf_eq, zero_smul, add_zero] using hz
  have hmap : ContDiffOn ℝ ∞
      (fun ζ : ℂ => (z + ζ • d, Real.exp (2 * (w + ζ * τ).re))) S := by
    have hlinear : ContDiff ℝ ∞ (fun ζ : ℂ => w + ζ * τ) := by fun_prop
    have hclock : ContDiff ℝ ∞ (fun ζ : ℂ => Real.exp (2 * (w + ζ * τ).re)) :=
      (contDiff_const.mul (Complex.reCLM.contDiff.comp hlinear)).exp
    exact (show ContDiff ℝ ∞ (fun ζ : ℂ => z + ζ • d) from by fun_prop).contDiffOn.prodMk
      hclock.contDiffOn
  have hH (i j : Fin n) : ContDiffOn ℝ ∞
      (fun ζ : ℂ => spacetimeMetricLine h x z d w τ ζ i j) S := by
    exact (Alignment.Y03Proof.metricFamily_hMat_contDiffOn hflow.1.2.1 x i j).comp hmap
      (fun ζ hζ => ⟨hζ, (Real.exp_pos _).le⟩)
  have hpos (ζ : ℂ) (hζ : ζ ∈ S) :
      (spacetimeMetricLine h x z d w τ ζ).PosDef :=
    Alignment.Y03Proof.hMat_posDef _ x _ hζ
  apply curvature_quadratic_nonneg_of_affine_dual
    (spacetimeMetricLine h x z d w τ) S hS hzero hH hpos
  intro ξ ν
  let η : ℂ → ComplexVector n := fun ζ => WithLp.toLp 2 (fun i => ξ i + ζ * ν i)
  have hη : ContDiff ℂ ∞ η := by
    apply (contDiff_piLp 2).mpr
    intro i
    change ContDiff ℂ ∞ (fun ζ => ξ i + ζ * ν i)
    fun_prop
  let γ : ℂ → ComplexVector n × ComplexVector n × ℂ :=
    fun ζ => (z + ζ • d, η ζ, w + ζ * τ)
  have hγ : ContDiffAt ℂ 2 γ 0 := by
    have hfirst : ContDiffAt ℂ 2 (fun ζ : ℂ => z + ζ • d) 0 := by fun_prop
    have hlast : ContDiffAt ℂ 2 (fun ζ : ℂ => w + ζ * τ) 0 := by fun_prop
    exact hfirst.prodMk ((hη.contDiffAt.of_le (by simp)).prodMk hlast)
  have hchart : (γ 0).1 ∈ chartTarget x := by
    simpa only [γ, zero_smul, add_zero] using hz
  have hcurve := localizedFlow_jointLevi_curve hflow hjoint x γ 0 hγ hchart
  simpa only [γ, η, spacetimeMetricLine, dualNormChart] using hcurve

end Yau.NodeProofs.C01Aux
