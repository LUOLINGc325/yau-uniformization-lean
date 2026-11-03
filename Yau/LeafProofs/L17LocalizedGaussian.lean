import Yau.LeafProofs.L17FrozenHeatLinearity
import Yau.LeafProofs.L17LocalizedSourceCoupling

/-! The literal localized Gaussian solution, with its initial value and linearity. -/

noncomputable section

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SourceLocalizationAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def localGaussian (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) : Point n → ℝ :=
  P.charts.frozenPhysicalHeat P.radius p (localizedSource P T hT f p)

theorem localGaussian_eq_unscale (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) :
    localGaussian P T hT f p =
      parabolicUnscale P.radius (P.charts.frozenHeatDuhamel p (rescaledSource P T hT f p)) := rfl

theorem localGaussian_initial (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (x : Space n) :
    localGaussian P T hT f p (x, 0) = 0 :=
  P.charts.frozenPhysicalHeat_initial P.radius p _ x

theorem localGaussian_smul (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (c : ℝ) (f : HolderSpace P T γ) (p : P.centers) (q : Point n) :
    localGaussian P T hT (c • f) p q = c * localGaussian P T hT f p q := by
  unfold localGaussian
  rw [localizedSource_smul, P.charts.frozenPhysicalHeat_smul]

theorem localGaussian_add (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f h : HolderSpace P T γ) (p : P.centers) (q : Point n) (ht : 0 ≤ q.2) :
    localGaussian P T hT (f + h) p q =
      localGaussian P T hT f p q + localGaussian P T hT h p q := by
  unfold localGaussian
  rw [localizedSource_add]
  exact P.charts.frozenPhysicalHeat_add P.radius p
    (localizedSource_continuous P T hT f p) (localizedSource_continuous P T hT h p)
    (localizedSource_abs_le_norm P T hT f p) (localizedSource_abs_le_norm P T hT h p) q ht

theorem localGaussian_equation (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (hSmall : T ≤ P.radius ^ 2) {γ F : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (f : HolderSpace P T γ) (p : P.centers)
    (hf : HolderBound γ Set.univ (rescaledSource P T hT.le f p) F)
    {q : Point n} (hq : q ∈ cylinder Set.univ 0 T) :
    linearOp (cylinder Set.univ 0 T)
      (fun _ => scalarSymbol (pullbackMatrix g (P.charts.chart p) 0)) (fun _ _ => 0)
      (localGaussian P T hT.le f p) q = localizedSource P T hT.le f p q :=
  P.charts.frozenPhysicalHeat_equation P.radius_pos hT hSmall hγ hγ1 p
    (L16Aux.holderBound_mono hf (Set.subset_univ _)) hq

end Yau.LeafProofs.L17Aux
