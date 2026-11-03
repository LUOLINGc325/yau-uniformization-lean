import Yau.LeafProofs.L17GaussianTermEquation
import Yau.LeafProofs.L17ParabolicOperator

/-! The actual Gaussian parametrix residual equals P Q - id on the original closed cylinder. -/

open Set Metric
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux

open Yau.Parabolic L17HolderAux L17SchauderAux L17SourceLocalizationAux L17LocalizedSchauderAux L17ParabolicOperatorAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem gaussian_schauder_time_eq_sum (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    {γ : ℝ} (f : HolderSpace P T γ) (u : SchauderSpace P T γ hT)
    (hValue : schauderFun u=gaussianParametrixFun P T hT.le f)
    (hu : ∀ p,C2 (cylinder Set.univ 0 T) (localGaussian P T hT.le f p))
    (x : M.Carrier) (t : Time T) :
    timeFun u (x,t)=∑ᶠ p,gaussianTimeTerm P T hT.le f p (x,t) := by
  have hX := schauderFun_hasDerivWithinAt u x t
  change HasDerivWithinAt (fun τ => schauderFun u (x,projIcc (0 : ℝ) T hT.le τ))
    (timeFun u (x,t)) (Icc (0 : ℝ) T) (t : ℝ) at hX
  rw [hValue] at hX
  have hG := gaussianParametrixFun_hasDerivWithinAt P T hT.le f hu x t
  exact (hX.derivWithin (uniqueDiffOn_Icc hT t t.property)).symm.trans
    (hG.derivWithin (uniqueDiffOn_Icc hT t t.property))

theorem gaussianParametrixFun_equation (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (hSmall : T ≤ P.radius^2) (hRadius : 2*P.radius < P.charts.radius)
    {γ C : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) (f : HolderSpace P T γ)
    (hf : ∀ p,HolderBound γ Set.univ (rescaledSource P T hT.le f p) C)
    (x : M.Carrier) (t : Time T) :
    (∑ᶠ p,gaussianTimeTerm P T hT.le f p (x,t))-
      laplacian g (fun y => gaussianParametrixFun P T hT.le f (y,t)) x =
      holderFun f (x,t)+gaussianResidualFun P T hT.le f (x,t) := by
  have hu p := localGaussian_c2_of_source_holder P T hT hSmall hγ hγ1 f p (hf p)
  let lap : P.centers → Cylinder M T → ℝ := fun p q =>
    laplacian g (fun y => gaussianTerm P T hT.le f p (y,q.2)) q.1
  let wt : P.centers → Cylinder M T → ℝ := fun p q => P.weight p q.1*holderFun f q
  let rr : P.centers → Cylinder M T → ℝ := fun p => rawLocalizedTerm P T p (physicalGaussianResidual P T hT.le f p)
  have hLapZero : ∀ (p : P.centers) (q : Cylinder M T),q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → lap p q=0 :=
    fun p q hq => gaussianTerm_laplacian_zero_of_not_cover P T hT.le f p q.1 q.2 hq
  have hTimeZero : ∀ (p : P.centers) (q : Cylinder M T),q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → gaussianTimeTerm P T hT.le f p q=0 :=
    fun p q hq => localizedTerm_zero_of_not_cover P T p _ q hq
  have hWeightZero : ∀ (p : P.centers) (q : Cylinder M T),q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → wt p q=0 := by
    intro p q hq
    have h := P.localization_mul_weight p q.1
    rw [localization_zero_of_not_cover P p hq,zero_mul] at h
    change P.weight p q.1*holderFun f q=0
    rw [← h,zero_mul]
  have hRZero : ∀ (p : P.centers) (q : Cylinder M T),q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → rr p q=0 :=
    fun p q hq => rawLocalizedTerm_zero_of_not_cover P T p _ q hq
  have hNeg := supported_finsum_smul P T lap (-1) hLapZero (x,t)
  simp only [neg_one_smul] at hNeg
  have hAdd := supported_finsum_add P T (gaussianTimeTerm P T hT.le f) (fun p q => -lap p q)
    hTimeZero (fun p q hq => by rw [hLapZero p q hq,neg_zero]) (x,t)
  have hDiff : (∑ᶠ p,gaussianTimeTerm P T hT.le f p (x,t))-(∑ᶠ p,lap p (x,t)) =
      ∑ᶠ p,(gaussianTimeTerm P T hT.le f p (x,t)-lap p (x,t)) := by
    simpa only [sub_eq_add_neg,hNeg] using hAdd.symm
  have hWeightSum : (∑ᶠ p,wt p (x,t))=holderFun f (x,t) := by
    change (∑ᶠ p,P.weight p x*holderFun f (x,t))=holderFun f (x,t)
    rw [← finsum_mul,P.weight_sum,one_mul]
  calc
    _ = ∑ᶠ p,(gaussianTimeTerm P T hT.le f p (x,t)-lap p (x,t)) := by
      rw [gaussianParametrixFun_laplacian P T hT.le f hu]
      exact hDiff
    _ = ∑ᶠ p,(wt p (x,t)+rr p (x,t)) :=
      finsum_congr (fun p => gaussianTerm_equation P T hT hSmall hRadius hγ hγ1 f p (hf p) x t)
    _ = (∑ᶠ p,wt p (x,t))+(∑ᶠ p,rr p (x,t)) := supported_finsum_add P T wt rr hWeightZero hRZero (x,t)
    _ = _ := by rw [hWeightSum]; rfl

theorem scalarParabolic_gaussian_residual (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (hSmall : T ≤ P.radius^2) (hr : P.radius ≤ 1) (hRadius : 2*P.radius < P.charts.radius)
    {γ C : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1) (f : HolderSpace P T γ) (u : SchauderSpace P T γ hT)
    (hValue : schauderFun u=gaussianParametrixFun P T hT.le f)
    (hf : ∀ p,HolderBound γ Set.univ (rescaledSource P T hT.le f p) C) (q : Cylinder M T) :
    holderFun (scalarParabolicCLM P T γ hT hSmall hγ1.le hr u) q =
      holderFun f q+gaussianResidualFun P T hT.le f q := by
  have hu p := localGaussian_c2_of_source_holder P T hT hSmall hγ hγ1 f p (hf p)
  rw [scalarParabolicCLM_value,gaussian_schauder_time_eq_sum P T hT f u hValue hu,hValue]
  exact gaussianParametrixFun_equation P T hT hSmall hRadius hγ hγ1 f hf q.1 q.2

theorem gaussian_operator_residual_value (P : UniformChartPartition g) (T : ℝ) (hT : 0 < T)
    (hSmall : T ≤ P.radius^2) (hr : P.radius ≤ 1) (hRadius : 2*P.radius < P.charts.radius)
    {γ C : ℝ} (hγ : 0 < γ) (hγ1 : γ < 1)
    (Q : HolderSpace P T γ →L[ℝ] SchauderSpace P T γ hT)
    (hValue : ∀ f,schauderFun (Q f)=gaussianParametrixFun P T hT.le f)
    (f : HolderSpace P T γ) (hf : ∀ p,HolderBound γ Set.univ (rescaledSource P T hT.le f p) C)
    (q : Cylinder M T) :
    holderFun (((scalarParabolicCLM P T γ hT hSmall hγ1.le hr).comp Q-
      ContinuousLinearMap.id ℝ (HolderSpace P T γ)) f) q =
      gaussianResidualFun P T hT.le f q := by
  change holderFun (scalarParabolicCLM P T γ hT hSmall hγ1.le hr (Q f)) q-holderFun f q = _
  rw [scalarParabolic_gaussian_residual P T hT hSmall hr hRadius hγ hγ1 f (Q f) (hValue f) hf]
  abel

end Yau.LeafProofs.L17Aux
