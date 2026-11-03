import Yau.Proofs.F01TensorDilation
import Yau.LeafProofs.L16SpatialTransport
import Yau.LeafProofs.L17ParabolicScaling

/-! Actual spatial jets under an affine parabolic chart change.
These identities hold for the genuine derivatives, independently of
any PDE or a priori regularity bound. -/
noncomputable section
open scoped ContDiff
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def affineParabolicPoint (ρ : ℝ) (c : Space n) (τ : ℝ) (p : Point n) : Point n :=
  (ρ • p.1 + c, τ + ρ ^ 2 * p.2)

def affineParabolicPullback (ρ : ℝ) (c : Space n) (τ : ℝ) (u : Point n → ℝ) : Point n → ℝ :=
  fun p => u (affineParabolicPoint ρ c τ p)

theorem affineParabolicPoint_continuous (ρ : ℝ) (c : Space n) (τ : ℝ) :
    Continuous (affineParabolicPoint ρ c τ) := by
  unfold affineParabolicPoint
  fun_prop

theorem spatialD_affineParabolicPullback (ρ : ℝ) (c : Space n) (τ : ℝ)
    (u : Point n → ℝ) (p : Point n) :
    spatialD (affineParabolicPullback ρ c τ u) p =
      ρ • spatialD u (affineParabolicPoint ρ c τ p) := by
  change fderiv ℝ (fun x : Space n =>
    (fun y => u (y + c, τ + ρ ^ 2 * p.2)) (ρ • x)) p.1 = _
  have hd := fderiv_comp_smul (𝕜 := ℝ)
    (f := fun y : Space n => u (y + c, τ + ρ ^ 2 * p.2)) (x := p.1) ρ
  rw [hd, fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun y : Space n => u (y, τ + ρ ^ 2 * p.2)) (x := ρ • p.1) c]
  rfl

theorem spatialDD_affineParabolicPullback (ρ : ℝ) (c : Space n) (τ : ℝ)
    (u : Point n → ℝ) (p : Point n) :
    spatialDD (affineParabolicPullback ρ c τ u) p =
      ρ ^ 2 • spatialDD u (affineParabolicPoint ρ c τ p) := by
  have hfun : (fun x : Space n => spatialD (affineParabolicPullback ρ c τ u) (x, p.2)) =
      (fun x => ρ • spatialD u (ρ • x + c, τ + ρ ^ 2 * p.2)) :=
    funext (fun x => spatialD_affineParabolicPullback ρ c τ u (x, p.2))
  change fderiv ℝ (fun x : Space n => spatialD (affineParabolicPullback ρ c τ u) (x, p.2)) p.1 = _
  rw [hfun]
  change fderiv ℝ (ρ • (fun x : Space n =>
    (fun y => spatialD u (y + c, τ + ρ ^ 2 * p.2)) (ρ • x))) p.1 = _
  rw [fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ), Pi.smul_apply]
  have hd := fderiv_comp_smul (𝕜 := ℝ)
    (f := fun y : Space n => spatialD u (y + c, τ + ρ ^ 2 * p.2)) (x := p.1) ρ
  rw [hd, fderiv_comp_add_right (𝕜 := ℝ)
    (f := fun y : Space n => spatialD u (y, τ + ρ ^ 2 * p.2)) (x := ρ • p.1) c,
    smul_smul, ← sq]
  rfl

end Yau.NodeProofs.F01Aux
