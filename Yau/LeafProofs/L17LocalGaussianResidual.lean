import Yau.LeafProofs.L17ScalarHessianProduct
import Yau.LeafProofs.L17LocalizedGaussianBounds
import Yau.LeafProofs.L17ParabolicOperatorCoefficients

/-! The literal coefficient and cutoff commutator of one actual Gaussian term. -/

open Set Metric
open scoped ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SourceLocalizationAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem localGaussian_c2_of_source_holder (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (hSmall : T ≤ P.radius ^ 2) {γ F : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (f : HolderSpace P T γ) (p : P.centers)
    (hf : HolderBound γ Set.univ (rescaledSource P T hT.le f p) F) :
    C2 (cylinder Set.univ 0 T) (localGaussian P T hT.le f p) := by
  obtain ⟨K, _, hbound⟩ := P.charts.frozenHeatDuhamel_controlled_bounds hγ hγ1
  have hS : 0 < T / P.radius ^ 2 := div_pos hT (sq_pos_of_pos P.radius_pos)
  have hSone : T / P.radius ^ 2 ≤ 1 := (div_le_one (sq_pos_of_pos P.radius_pos)).mpr hSmall
  have hu := hbound p (T / P.radius ^ 2) F hS hSone
    (rescaledSource P T hT.le f p) (L16Aux.holderBound_mono hf (subset_univ _))
  rw [localGaussian_eq_unscale]
  exact c2_parabolicUnscale P.radius_pos.ne' hT hu.1.1

def localGaussianResidual (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Point n) : ℝ :=
  let χ := fun z => P.localization p (P.charts.chart p z)
  let v := localGaussian P T hT f p
  let a := chartCoefficient P.charts p q.1
  χ q.1 * realHessianContraction (chartCoefficient P.charts p 0 - a) (fun z => v (z,q.2)) q.1 -
    v q * realHessianContraction a χ q.1 - gradientCrossContraction a χ (fun z => v (z,q.2)) q.1

theorem localGaussianResidual_equation (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (hSmall : T ≤ P.radius ^ 2) (hRadius : 2 * P.radius < P.charts.radius)
    {γ F : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) (f : HolderSpace P T γ) (p : P.centers)
    (hf : HolderBound γ Set.univ (rescaledSource P T hT.le f p) F)
    {q : Point n} (hq : q ∈ cylinder (ball (0 : ComplexVector n) (2 * P.radius)) 0 T) :
    linearOp (cylinder Set.univ 0 T) (fun r => chartCoefficient P.charts p r.1) (fun _ _ => 0)
      (fun r => P.localization p (P.charts.chart p r.1) * localGaussian P T hT.le f p r) q =
      P.localization p (P.charts.chart p q.1) * localizedSource P T hT.le f p q +
        localGaussianResidual P T hT.le f p q := by
  have hq' : q ∈ cylinder Set.univ 0 T := ⟨mem_univ _,hq.2⟩
  have hχ : ContDiffAt ℝ 2 (fun z => P.localization p (P.charts.chart p z)) q.1 :=
    ((smoothFn_comp_backgroundChart_contDiffOn P.charts (P.localization_smooth p) p).contDiffAt
      (isOpen_ball.mem_nhds ((ball_subset_ball hRadius.le) hq.1))).of_le (by simp)
  have heq := linearOp_spatial_mul_frozen
    (localGaussian_c2_of_source_holder P T hT hSmall hγ hγ1 f p hf)
    (fun z => P.localization p (P.charts.chart p z)) (chartCoefficient P.charts p 0)
    (fun r => chartCoefficient P.charts p r.1) hq' hχ
  rw [show chartCoefficient P.charts p 0 = scalarSymbol (pullbackMatrix g (P.charts.chart p) 0) from rfl,
    localGaussian_equation P T hT hSmall hγ hγ1 f p hf hq'] at heq
  simpa only [localGaussianResidual,chartCoefficient,sub_eq_add_neg,add_assoc] using heq

end Yau.LeafProofs.L17Aux
