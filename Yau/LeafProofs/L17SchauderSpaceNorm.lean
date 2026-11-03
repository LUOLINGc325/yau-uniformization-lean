import Yau.LeafProofs.L17SchauderSpaceDerivatives
import Mathlib.Analysis.Calculus.TangentCone.Real

open Set Metric
open scoped Topology
noncomputable section
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17SchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}
  {P : UniformChartPartition g} {T gamma : ℝ} {hT : 0 < T}

theorem gradientFun_eq_of_function_eq {u v : SchauderSpace P T gamma hT}
    (huv : schauderFun u = schauderFun v) : gradientFun u = gradientFun v := by
  funext q
  rcases q with ⟨p,z,t⟩
  have hEq : chartFunction u p t = chartFunction v p t := funext (fun y => congrFun huv (P.charts.chart p y,t))
  have hu := chartFunction_hasFDerivAt u p t z.property
  rw [hEq] at hu
  exact hu.unique (chartFunction_hasFDerivAt v p t z.property)

theorem hessianFun_eq_of_function_eq {u v : SchauderSpace P T gamma hT}
    (huv : schauderFun u = schauderFun v) : hessianFun u = hessianFun v := by
  have hGrad := gradientFun_eq_of_function_eq huv
  funext q
  rcases q with ⟨p,z,t⟩
  have hEq : chartGradient u p t = chartGradient v p t := by
    funext y
    simp only [chartGradient,hGrad]
  have hu := chartGradient_hasFDerivAt u p t z.property
  rw [hEq] at hu
  exact hu.unique (chartGradient_hasFDerivAt v p t z.property)

theorem timeFun_eq_of_function_eq {u v : SchauderSpace P T gamma hT}
    (huv : schauderFun u = schauderFun v) : timeFun u = timeFun v := by
  funext q
  rcases q with ⟨x,t⟩
  have hEq : (fun tau => schauderFun u (closedTimePath T hT x tau)) =
      (fun tau => schauderFun v (closedTimePath T hT x tau)) := funext (fun tau => congrFun huv _)
  have hu := schauderFun_hasDerivWithinAt u x t
  rw [hEq] at hu
  exact (hu.derivWithin (uniqueDiffOn_Icc hT (t : ℝ) t.property)).symm.trans
    ((schauderFun_hasDerivWithinAt v x t).derivWithin (uniqueDiffOn_Icc hT (t : ℝ) t.property))

/-- The actual global function, including the closed time endpoints,
determines all the genuine derivatives and hence the entire Banach element. -/
theorem schauderFun_injective : Function.Injective (schauderFun (P := P) (T := T) (gamma := gamma) (hT := hT)) := by
  intro u v huv
  have h0 : u.val.1.1 = v.val.1.1 := by
    apply holderFun_injective P T gamma
    funext q
    apply mul_left_cancel₀ (pow_ne_zero 2 P.radius_pos.ne')
    exact congrFun huv q
  have h1 : u.val.1.2 = v.val.1.2 := by
    apply localFun_injective (D1 n) P T gamma
    funext q
    apply smul_right_injective (D1 n) P.radius_pos.ne'
    exact congrFun (gradientFun_eq_of_function_eq huv) q
  have h2 : u.val.2.1 = v.val.2.1 := by
    apply localFun_injective (D2 n) P T gamma
    exact hessianFun_eq_of_function_eq huv
  have h3 : u.val.2.2 = v.val.2.2 := by
    apply holderFun_injective P T gamma
    exact timeFun_eq_of_function_eq huv
  exact Subtype.ext (Prod.ext (Prod.ext h0 h1) (Prod.ext h2 h3))

theorem functionCLM_injective (P : UniformChartPartition g) (T gamma : ℝ) (hT : 0 < T) :
    Function.Injective (functionCLM P T gamma hT) := by
  intro u v huv
  apply schauderFun_injective
  exact funext (fun q => congrArg (fun f : BoundedContinuousFunction (Cylinder M T) ℝ => f q) huv)

theorem norm_zero_iff_actual_function_zero (u : SchauderSpace P T gamma hT) :
    ‖u‖ = 0 ↔ ∀ q, schauderFun u q = 0 := by
  constructor
  · intro hu q
    have h := norm_eq_zero.mp hu
    subst u
    change (functionCLM P T gamma hT 0) q = 0
    rw [(functionCLM P T gamma hT).map_zero]
    rfl
  · intro hu
    have h : u = 0 := by
      apply schauderFun_injective
      funext q
      rw [hu q]
      change 0 = (functionCLM P T gamma hT 0) q
      rw [(functionCLM P T gamma hT).map_zero]
      rfl
    rw [h,norm_zero]

theorem functionHolder_norm_le (u : SchauderSpace P T gamma hT) :
    ‖functionHolderCLM P T gamma hT u‖ ≤ P.radius^2*‖u‖ := by
  change ‖P.radius^2 • u.val.1.1‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _)]
  exact mul_le_mul_of_nonneg_left ((le_max_left _ _).trans (le_max_left _ _)) (sq_nonneg _)

theorem gradientHolder_norm_le (u : SchauderSpace P T gamma hT) :
    ‖gradientHolderCLM P T gamma hT u‖ ≤ P.radius*‖u‖ := by
  change ‖P.radius • u.val.1.2‖ ≤ _
  rw [norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos]
  exact mul_le_mul_of_nonneg_left ((le_max_right _ _).trans (le_max_left _ _)) P.radius_pos.le

theorem hessianHolder_norm_le (u : SchauderSpace P T gamma hT) :
    ‖hessianHolderCLM P T gamma hT u‖ ≤ ‖u‖ := (le_max_left _ _).trans (le_max_right _ _)
theorem timeHolder_norm_le (u : SchauderSpace P T gamma hT) :
    ‖timeHolderCLM P T gamma hT u‖ ≤ ‖u‖ := (le_max_right _ _).trans (le_max_right _ _)

/-- Exact scaled norm equality, with no unspecified radius-dependent factor. -/
theorem norm_eq_scaled_actual_jets (u : SchauderSpace P T gamma hT) :
    ‖u‖ = max
      (max ((P.radius^2)⁻¹*‖functionHolderCLM P T gamma hT u‖)
        (P.radius⁻¹*‖gradientHolderCLM P T gamma hT u‖))
      (max ‖hessianHolderCLM P T gamma hT u‖ ‖timeHolderCLM P T gamma hT u‖) := by
  have h0 : (P.radius^2)⁻¹*‖functionHolderCLM P T gamma hT u‖ = ‖u.val.1.1‖ := by
    change _*‖P.radius^2 • u.val.1.1‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg (sq_nonneg _),← mul_assoc,
      inv_mul_cancel₀ (pow_ne_zero 2 P.radius_pos.ne'),one_mul]
  have h1 : P.radius⁻¹*‖gradientHolderCLM P T gamma hT u‖ = ‖u.val.1.2‖ := by
    change _*‖P.radius • u.val.1.2‖ = _
    rw [norm_smul,Real.norm_eq_abs,abs_of_pos P.radius_pos,← mul_assoc,inv_mul_cancel₀ P.radius_pos.ne',one_mul]
  rw [h0,h1]
  rfl

theorem function_holder_bounds (u : SchauderSpace P T gamma hT) :
    (∀ q, |schauderFun u q| ≤ P.radius^2*‖u‖) ∧
    ∀ i : ChartPairs P T, |pairWeight P T gamma i*
      (schauderFun u (chartRight P T i)-schauderFun u (chartLeft P T i))| ≤ P.radius^2*‖u‖ :=
  ⟨fun q => (value_abs_le_norm (functionHolderCLM P T gamma hT u) q).trans (functionHolder_norm_le u),
    fun i => (weighted_difference_abs_le_norm (functionHolderCLM P T gamma hT u) i).trans (functionHolder_norm_le u)⟩

theorem gradient_holder_bounds (u : SchauderSpace P T gamma hT) :
    (∀ q, ‖gradientFun u q‖ ≤ P.radius*‖u‖) ∧
    ∀ i : ChartPairs P T, ‖pairWeight P T gamma i •
      (gradientFun u (localRight P T i)-gradientFun u (localLeft P T i))‖ ≤ P.radius*‖u‖ :=
  ⟨fun q => (localValue_norm_le (D1 n) (gradientHolderCLM P T gamma hT u) q).trans (gradientHolder_norm_le u),
    fun i => (localWeighted_difference_norm_le (D1 n) (gradientHolderCLM P T gamma hT u) i).trans (gradientHolder_norm_le u)⟩

theorem hessian_holder_bounds (u : SchauderSpace P T gamma hT) :
    (∀ q, ‖hessianFun u q‖ ≤ ‖u‖) ∧
    ∀ i : ChartPairs P T, ‖pairWeight P T gamma i •
      (hessianFun u (localRight P T i)-hessianFun u (localLeft P T i))‖ ≤ ‖u‖ :=
  ⟨fun q => (localValue_norm_le (D2 n) (hessianHolderCLM P T gamma hT u) q).trans (hessianHolder_norm_le u),
    fun i => (localWeighted_difference_norm_le (D2 n) (hessianHolderCLM P T gamma hT u) i).trans (hessianHolder_norm_le u)⟩

theorem time_holder_bounds (u : SchauderSpace P T gamma hT) :
    (∀ q, |timeFun u q| ≤ ‖u‖) ∧ ∀ i : ChartPairs P T,
      |pairWeight P T gamma i*(timeFun u (chartRight P T i)-timeFun u (chartLeft P T i))| ≤ ‖u‖ :=
  ⟨fun q => (value_abs_le_norm (timeHolderCLM P T gamma hT u) q).trans (timeHolder_norm_le u),
    fun i => (weighted_difference_abs_le_norm (timeHolderCLM P T gamma hT u) i).trans (timeHolder_norm_le u)⟩

variable (P T gamma hT)

def schauderEvalCLM (q : Cylinder M T) : SchauderSpace P T gamma hT →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (functionCLM P T gamma hT)
def gradientEvalCLM (q : LocalCylinder P T) : SchauderSpace P T gamma hT →L[ℝ] D1 n :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (gradientCLM P T gamma hT)
def hessianEvalCLM (q : LocalCylinder P T) : SchauderSpace P T gamma hT →L[ℝ] D2 n :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (hessianCLM P T gamma hT)
def timeEvalCLM (q : Cylinder M T) : SchauderSpace P T gamma hT →L[ℝ] ℝ :=
  (BoundedContinuousFunction.evalCLM ℝ q).comp (timeCLM P T gamma hT)

theorem schauderEvalCLM_opNorm_le (q : Cylinder M T) : ‖schauderEvalCLM P T gamma hT q‖ ≤ P.radius^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro u
  change ‖schauderFun u q‖ ≤ _
  simpa only [Real.norm_eq_abs] using (function_holder_bounds u).1 q

theorem gradientEvalCLM_opNorm_le (q : LocalCylinder P T) : ‖gradientEvalCLM P T gamma hT q‖ ≤ P.radius := by
  apply ContinuousLinearMap.opNorm_le_bound _ P.radius_pos.le
  intro u
  exact (gradient_holder_bounds u).1 q

theorem hessianEvalCLM_opNorm_le (q : LocalCylinder P T) : ‖hessianEvalCLM P T gamma hT q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖hessianFun u q‖ ≤ _
  simpa only [one_mul] using (hessian_holder_bounds u).1 q

theorem timeEvalCLM_opNorm_le (q : Cylinder M T) : ‖timeEvalCLM P T gamma hT q‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  change ‖timeFun u q‖ ≤ _
  simpa only [Real.norm_eq_abs,one_mul] using (time_holder_bounds u).1 q

theorem functionHolderCLM_opNorm_le : ‖functionHolderCLM P T gamma hT‖ ≤ P.radius^2 :=
  ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _) functionHolder_norm_le

theorem gradientHolderCLM_opNorm_le : ‖gradientHolderCLM P T gamma hT‖ ≤ P.radius :=
  ContinuousLinearMap.opNorm_le_bound _ P.radius_pos.le gradientHolder_norm_le

theorem hessianHolderCLM_opNorm_le : ‖hessianHolderCLM P T gamma hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using hessianHolder_norm_le u

theorem timeHolderCLM_opNorm_le : ‖timeHolderCLM P T gamma hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  simpa only [one_mul] using timeHolder_norm_le u

theorem functionCLM_opNorm_le : ‖functionCLM P T gamma hT‖ ≤ P.radius^2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
  intro u
  apply (BoundedContinuousFunction.norm_le (mul_nonneg (sq_nonneg _) (norm_nonneg _))).mpr
  intro q
  change ‖schauderFun u q‖ ≤ _
  simpa only [Real.norm_eq_abs] using (function_holder_bounds u).1 q

theorem gradientCLM_opNorm_le : ‖gradientCLM P T gamma hT‖ ≤ P.radius := by
  apply ContinuousLinearMap.opNorm_le_bound _ P.radius_pos.le
  intro u
  apply (BoundedContinuousFunction.norm_le (mul_nonneg P.radius_pos.le (norm_nonneg _))).mpr
  intro q
  exact (gradient_holder_bounds u).1 q

theorem hessianCLM_opNorm_le : ‖hessianCLM P T gamma hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  apply (BoundedContinuousFunction.norm_le (mul_nonneg zero_le_one (norm_nonneg _))).mpr
  intro q
  change ‖hessianFun u q‖ ≤ _
  simpa only [one_mul] using (hessian_holder_bounds u).1 q

theorem timeCLM_opNorm_le : ‖timeCLM P T gamma hT‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  apply (BoundedContinuousFunction.norm_le (mul_nonneg zero_le_one (norm_nonneg _))).mpr
  intro q
  change ‖timeFun u q‖ ≤ _
  simpa only [Real.norm_eq_abs,one_mul] using (time_holder_bounds u).1 q

theorem schauderEvalCLM_eq_actual (u : SchauderSpace P T gamma hT) (q : Cylinder M T) :
    schauderEvalCLM P T gamma hT q u = schauderFun u q := rfl

theorem gradientEvalCLM_eq_fderiv (u : SchauderSpace P T gamma hT) (p : P.centers)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    gradientEvalCLM P T gamma hT ⟨p,(z,t)⟩ u = fderiv ℝ (chartFunction u p t) z :=
  (chartFunction_hasFDerivAt u p t z.property).fderiv.symm

theorem hessianEvalCLM_eq_second_fderiv (u : SchauderSpace P T gamma hT) (p : P.centers)
    (z : ↥(ball (0 : ComplexVector n) P.radius)) (t : Time T) :
    hessianEvalCLM P T gamma hT ⟨p,(z,t)⟩ u = fderiv ℝ (fderiv ℝ (chartFunction u p t)) z :=
  (chartFunction_hasSecondFDerivAt u p t z.property).fderiv.symm

theorem timeEvalCLM_eq_derivWithin (u : SchauderSpace P T gamma hT) (x : M.Carrier) (t : Time T) :
    timeEvalCLM P T gamma hT (x,t) u =
      derivWithin (fun tau => schauderFun u (closedTimePath T hT x tau)) (Icc (0 : ℝ) T) t :=
  ((schauderFun_hasDerivWithinAt u x t).derivWithin (uniqueDiffOn_Icc hT (t : ℝ) t.property)).symm

end Yau.LeafProofs.L17SchauderAux
