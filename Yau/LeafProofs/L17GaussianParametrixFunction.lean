import Yau.LeafProofs.L17LocalizedGaussianBounds
import Yau.LeafProofs.L17LocalizedSchauderTimeTransport

/-! The actual locally finite Gaussian parametrix as a function on the closed cylinder. -/

open Set Metric
noncomputable section

namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SourceLocalizationAux L17LocalizedSchauderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def gaussianTerm (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) : Cylinder M T → ℝ :=
  localizedTerm P T p (fun q => localGaussian P T hT f p (q.1,(q.2 : ℝ)))

def gaussianParametrixFun (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (q : Cylinder M T) : ℝ :=
  ∑ᶠ p, gaussianTerm P T hT f p q

theorem gaussianTerm_zero_of_not_cover (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (p : P.centers) (q : Cylinder M T)
    (hx : q.1 ∉ P.charts.chart p '' closedBall 0 P.radius) : gaussianTerm P T hT f p q = 0 :=
  localizedTerm_zero_of_not_cover P T p _ q hx

theorem gaussianTerm_add (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f h : HolderSpace P T γ) (p : P.centers) (q : Cylinder M T) :
    gaussianTerm P T hT (f + h) p q = gaussianTerm P T hT f p q + gaussianTerm P T hT h p q := by
  change P.localization p q.1 * localGaussian P T hT (f + h) p _ = _
  rw [localGaussian_add P T hT f h p _ q.2.property.1, mul_add]
  rfl

theorem gaussianTerm_smul (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (c : ℝ) (f : HolderSpace P T γ) (p : P.centers) (q : Cylinder M T) :
    gaussianTerm P T hT (c • f) p q = c * gaussianTerm P T hT f p q := by
  change P.localization p q.1 * localGaussian P T hT (c • f) p _ = _
  rw [localGaussian_smul]
  change _ * (c * _) = c * (_ * _)
  ring

theorem gaussianParametrixFun_add (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f h : HolderSpace P T γ) (q : Cylinder M T) :
    gaussianParametrixFun P T hT (f + h) q =
      gaussianParametrixFun P T hT f q + gaussianParametrixFun P T hT h q := by
  simp only [gaussianParametrixFun, gaussianTerm_add]
  exact supported_finsum_add P T (gaussianTerm P T hT f) (gaussianTerm P T hT h)
    (gaussianTerm_zero_of_not_cover P T hT f) (gaussianTerm_zero_of_not_cover P T hT h) q

theorem gaussianParametrixFun_smul (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (c : ℝ) (f : HolderSpace P T γ) (q : Cylinder M T) :
    gaussianParametrixFun P T hT (c • f) q = c * gaussianParametrixFun P T hT f q := by
  simp only [gaussianParametrixFun, gaussianTerm_smul]
  exact supported_finsum_smul P T (gaussianTerm P T hT f) c
    (gaussianTerm_zero_of_not_cover P T hT f) q

theorem gaussianParametrixFun_initial (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ) (x : M.Carrier) :
    gaussianParametrixFun P T hT f (x,⟨0,⟨le_rfl,hT⟩⟩) = 0 := by
  simp only [gaussianParametrixFun,gaussianTerm,localizedTerm,localGaussian_initial,mul_zero,finsum_zero]

theorem gaussianParametrixFun_continuous (P : UniformChartPartition g) (T : ℝ) (hT : 0 ≤ T)
    {γ : ℝ} (f : HolderSpace P T γ)
    (hu : ∀ p, C2 (cylinder Set.univ 0 T) (localGaussian P T hT f p)) :
    Continuous (gaussianParametrixFun P T hT f) := by
  change Continuous (globalSum P T (fun p q => localGaussian P T hT f p (q.1,(q.2 : ℝ))))
  apply globalSum_continuous
  intro p
  have hc : Continuous (fun q : ComplexVector n × Time T => (q.1,(q.2 : ℝ))) :=
    continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
  exact (hu p).1.comp hc.continuousOn (fun q _ => ⟨mem_univ _,q.2.property⟩)

end Yau.LeafProofs.L17Aux
