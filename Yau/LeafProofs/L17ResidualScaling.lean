import Yau.LeafProofs.L17UnitGaussianResidual
import Yau.LeafProofs.L17LocalGaussianResidual

open Set
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17ParabolicOperatorAux L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem secondFDeriv_comp_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (f : E → F) (ρ : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun z => f (ρ • z))) x = ρ^2 • fderiv ℝ (fderiv ℝ f) (ρ • x) := by
  have heq : fderiv ℝ (fun z => f (ρ • z)) = fun z => ρ • fderiv ℝ f (ρ • z) :=
    funext (fun z => fderiv_comp_smul (𝕜 := ℝ) (f := f) (x := z) ρ)
  rw [heq]
  change fderiv ℝ (ρ • (fun z => fderiv ℝ f (ρ • z))) x = _
  rw [fderiv_const_smul_field (𝕜 := ℝ) (R := ℝ)
    (f := fun z : E => fderiv ℝ f (ρ • z)) ρ,Pi.smul_apply,
    fderiv_comp_smul (𝕜 := ℝ) (f := fderiv ℝ f) (x := x) ρ,smul_smul,pow_two]

def parabolicForwardPoint {n : ℕ} (ρ : ℝ) (q : Point n) : Point n := (ρ • q.1,ρ^2*q.2)

theorem parabolicScalePoint_forward {n : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) (q : Point n) :
    parabolicScalePoint ρ (parabolicForwardPoint ρ q) = q := by
  apply Prod.ext
  · exact inv_smul_smul₀ hρ q.1
  · change (ρ^2)⁻¹*(ρ^2*q.2) = q.2
    rw [← mul_assoc,inv_mul_cancel₀ (pow_ne_zero 2 hρ),one_mul]

theorem parabolicForwardPoint_scale {n : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0) (q : Point n) :
    parabolicForwardPoint ρ (parabolicScalePoint ρ q) = q := by
  apply Prod.ext
  · exact smul_inv_smul₀ hρ q.1
  · change ρ^2*((ρ^2)⁻¹*q.2) = q.2
    rw [← mul_assoc,mul_inv_cancel₀ (pow_ne_zero 2 hρ),one_mul]

theorem scalarFrozenResidual_scaling {n : ℕ} {ρ : ℝ} (hρ : ρ ≠ 0)
    (a d : Point n → Mat n) (φ : Space n → ℝ) (v : Point n → ℝ) (q : Point n) :
    scalarFrozenResidual a d φ (parabolicUnscale ρ v) (parabolicForwardPoint ρ q) =
      scalarFrozenResidual (fun r => a (parabolicForwardPoint ρ r))
        (fun r => d (parabolicForwardPoint ρ r)) (fun z => φ (ρ • z)) v q := by
  have hD : spatialD (parabolicUnscale ρ v) (parabolicForwardPoint ρ q) = ρ • spatialD v q := by
    have hh := spatialD_parabolicUnscale hρ v (parabolicForwardPoint ρ q)
    change spatialD (parabolicUnscale ρ v) (parabolicForwardPoint ρ q) =
      ρ • spatialD v (parabolicScalePoint ρ (parabolicForwardPoint ρ q)) at hh
    rwa [parabolicScalePoint_forward hρ] at hh
  have hH : spatialDD (parabolicUnscale ρ v) (parabolicForwardPoint ρ q) = spatialDD v q := by
    have hh := spatialDD_parabolicUnscale hρ v (parabolicForwardPoint ρ q)
    change spatialDD (parabolicUnscale ρ v) (parabolicForwardPoint ρ q) =
      spatialDD v (parabolicScalePoint ρ (parabolicForwardPoint ρ q)) at hh
    rwa [parabolicScalePoint_forward hρ] at hh
  have hV : parabolicUnscale ρ v (parabolicForwardPoint ρ q) = ρ^2*v q := by
    change ρ^2*v (parabolicScalePoint ρ (parabolicForwardPoint ρ q)) = _
    rw [parabolicScalePoint_forward hρ]
  rw [scalarFrozenResidual_eq_sum,scalarFrozenResidual_eq_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [hD,hH,hV,fderiv_comp_smul (𝕜 := ℝ) (f := φ) (x := q.1) ρ,
    secondFDeriv_comp_smul φ ρ q.1]
  simp only [smul_apply,smul_eq_mul,parabolicForwardPoint]
  ring

theorem localGaussianResidual_forward (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Point n) :
    localGaussianResidual P T hT f p (parabolicForwardPoint P.radius q) =
      unitGaussianResidual P T hT f p q := by
  change scalarFrozenResidual (fun r => chartCoefficient P.charts p r.1)
    (fun r => chartCoefficient P.charts p 0-chartCoefficient P.charts p r.1)
    (fun z => P.localization p (P.charts.chart p z))
    (parabolicUnscale P.radius (P.charts.frozenHeatDuhamel p
      (L17SourceLocalizationAux.rescaledSource P T hT f p))) (parabolicForwardPoint P.radius q) = _
  exact scalarFrozenResidual_scaling P.radius_pos.ne' _ _ _ _ q

theorem localGaussianResidual_eq_unit (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Point n) :
    localGaussianResidual P T hT f p q =
      unitGaussianResidual P T hT f p (parabolicScalePoint P.radius q) := by
  have h := localGaussianResidual_forward P T hT f p (parabolicScalePoint P.radius q)
  rwa [parabolicForwardPoint_scale P.radius_pos.ne'] at h

end Yau.LeafProofs.L17Aux
