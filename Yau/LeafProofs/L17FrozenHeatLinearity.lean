import Yau.LeafProofs.L17FrozenPhysicalHeat

/-! Actual linearity of the rescaled frozen Gaussian convolution on bounded continuous sources. -/

noncomputable section

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem parabolicSourceRescale_add (ρ : ℝ) (f h : Point n → ℝ) :
    parabolicSourceRescale ρ (f + h) = parabolicSourceRescale ρ f + parabolicSourceRescale ρ h := rfl

theorem parabolicSourceRescale_smul (ρ c : ℝ) (f : Point n → ℝ) :
    parabolicSourceRescale ρ (c • f) = c • parabolicSourceRescale ρ f := rfl

theorem BoundedChartFamily.frozenPhysicalHeat_smul
    (A : BoundedChartFamily g) (ρ : ℝ) (p : M.Carrier) (c : ℝ) (f : Point n → ℝ) (q : Point n) :
    A.frozenPhysicalHeat ρ p (c • f) q = c * A.frozenPhysicalHeat ρ p f q := by
  change ρ ^ 2 * A.frozenHeatDuhamel p (parabolicSourceRescale ρ (c • f))
      (parabolicScalePoint ρ q) =
    c * (ρ ^ 2 * A.frozenHeatDuhamel p (parabolicSourceRescale ρ f) (parabolicScalePoint ρ q))
  rw [parabolicSourceRescale_smul, A.frozenHeatDuhamel_smul]
  ring

theorem BoundedChartFamily.frozenPhysicalHeat_add
    (A : BoundedChartFamily g) (ρ : ℝ) (p : M.Carrier) {F G : ℝ} {f h : Point n → ℝ}
    (hf : Continuous f) (hh : Continuous h) (hF : ∀ q, |f q| ≤ F) (hG : ∀ q, |h q| ≤ G)
    (q : Point n) (ht : 0 ≤ q.2) :
    A.frozenPhysicalHeat ρ p (f + h) q = A.frozenPhysicalHeat ρ p f q + A.frozenPhysicalHeat ρ p h q := by
  have hmap : Continuous (fun q : Point n => (ρ • q.1, ρ ^ 2 * q.2)) := by fun_prop
  have htime : 0 ≤ (parabolicScalePoint ρ q).2 :=
    mul_nonneg (inv_nonneg.mpr (sq_nonneg ρ)) ht
  have hAdd := A.frozenHeatDuhamel_add p (hf.comp hmap) (hh.comp hmap)
    (fun r => hF (ρ • r.1, ρ ^ 2 * r.2)) (fun r => hG (ρ • r.1, ρ ^ 2 * r.2))
    (parabolicScalePoint ρ q) htime
  change A.frozenHeatDuhamel p (parabolicSourceRescale ρ f + parabolicSourceRescale ρ h)
      (parabolicScalePoint ρ q) =
    A.frozenHeatDuhamel p (parabolicSourceRescale ρ f) (parabolicScalePoint ρ q) +
      A.frozenHeatDuhamel p (parabolicSourceRescale ρ h) (parabolicScalePoint ρ q) at hAdd
  change ρ ^ 2 * A.frozenHeatDuhamel p (parabolicSourceRescale ρ (f + h))
      (parabolicScalePoint ρ q) = _
  rw [parabolicSourceRescale_add, hAdd]
  change ρ ^ 2 * (_ + _) = ρ ^ 2 * _ + ρ ^ 2 * _
  dsimp only [parabolicScalePoint]
  ring

end Yau.LeafProofs.L17Aux
