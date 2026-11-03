import Yau.Proofs.G04LocalLeviIdentity

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ} {M : ComplexManifold n}

def scalarForm (f : M.Carrier → ℝ) : RealForm M 0 :=
  fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentVector M x) (Fin 0) (f x)

theorem scalarForm_components (f : M.Carrier → ℝ) (x : M.Carrier) (z : ComplexVector n)
    (I : Fin 0 → RIdx n) : formComponents (scalarForm f) x z I = inChart x f z := rfl

theorem scalarForm_smooth (f : M.Carrier → ℝ) (hf : SmoothFn f) : SmoothRealForm (scalarForm f) :=
  fun x _ => hf x

def tangentJ (x : M.Carrier) : TangentVector M x →L[ℝ] TangentVector M x :=
  (Complex.I • ContinuousLinearMap.id ℂ (TangentVector M x)).restrictScalars ℝ

def jPullbackForm (A : RealForm M 1) : RealForm M 1 :=
  fun x => (A x).compContinuousLinearMap (tangentJ x)

theorem I_smul_realVec (a : RIdx n) :
    Complex.I • realVec a = L12Aux.jSign a • realVec (L12Aux.jIndex n a) := by
  rcases a with ⟨a, ar⟩
  fin_cases ar <;> simp [realVec, L12Aux.jIndex, L12Aux.jSign, smul_smul]

theorem chartVec_real_smul (x y : M.Carrier) (r : ℝ) (u : ComplexVector n) :
    chartVec x y (r • u) = r • chartVec x y u :=
  (L03.chartRealContinuousLinearMap x y).map_smul r u

theorem jPullbackForm_components (A : RealForm M 1) (x : M.Carrier) (z : ComplexVector n)
    (I : Fin 1 → RIdx n) :
    formComponents (jPullbackForm A) x z I = L12Aux.jSign (I 0) *
      formComponents A x z (fun _ => L12Aux.jIndex n (I 0)) := by
  simp only [formComponents, jPullbackForm, ContinuousAlternatingMap.compContinuousLinearMap_apply,
    Function.comp_def]
  have hv : (fun r => tangentJ (chartInv x z) (chartVec x (chartInv x z) (realVec (I r)))) =
      (fun r : Fin 1 => L12Aux.jSign (I 0) •
        chartVec x (chartInv x z) (realVec (L12Aux.jIndex n (I 0)))) := by
    funext r
    have hr : r = 0 := Fin.eq_zero r
    subst r
    change Complex.I • chartVec x (chartInv x z) (realVec (I 0)) = _
    rw [← L12Aux.chartVec_complex_smul, I_smul_realVec, chartVec_real_smul]
  rw [hv, ContinuousAlternatingMap.map_smul_univ]
  simp only [Fin.prod_univ_one, smul_eq_mul]

def jDifferential (f : M.Carrier → ℝ) : RealForm M 1 :=
  jPullbackForm (L03.exteriorRealForm (scalarForm f))

theorem jDifferential_components (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin 1 → RIdx n) :
    formComponents (jDifferential f) x z I = jScalarComponents (inChart x f) z I := by
  rw [jDifferential, jPullbackForm_components,
    L03.exteriorRealForm_represents (scalarForm f) (scalarForm_smooth f hf) x z hz]
  simp [exteriorComponents, scalarForm_components, jScalarComponents]

theorem jDifferential_smooth (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    SmoothRealForm (jDifferential f) := by
  intro x I
  apply (contDiffOn_const.mul (L12Aux.rDeriv_contDiffOn
    (isOpen_extChartAt_target (I := ComplexModel n) x) (hf x) (L12Aux.jIndex n (I 0)))).congr
  intro z hz
  exact jDifferential_components f hf x hz I

def ddRealForm (f : M.Carrier → ℝ) : RealForm M 2 :=
  (-(1 / 2 : ℝ)) • L03.exteriorRealForm (jDifferential f)

theorem dd_coefficients (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) (I : Fin 2 → RIdx n) :
    formComponents (ddRealForm f) x z I =
      2 * (matrixPairing (leviC (inChart x f) z) (realVec (I 0)) (realVec (I 1))).im := by
  have hj := jDifferential_smooth f hf
  have heq : formComponents (jDifferential f) x =ᶠ[𝓝 z] jScalarComponents (inChart x f) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    funext J
    exact jDifferential_components f hf x hw J
  simp only [ddRealForm, L03.formComponents_smul, Pi.smul_apply, smul_eq_mul]
  rw [L03.exteriorRealForm_represents (jDifferential f) hj x z hz,
    congrFun (L03.exteriorComponents_congr_nhds heq) I]
  exact local_dd_levi (((hf x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)) I

theorem iotaRealForm_center_components (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ x, (A x).IsHermitian) (x : M.Carrier) (I : Fin 2 → RIdx n) :
    formComponents (iotaRealForm A hA) x (chartPt x x) I =
      2 * (matrixPairing (A x) (realVec (I 0)) (realVec (I 1))).im := by
  rw [L03.formComponents_apply_of_mem_source _ x x (mem_extChartAt_source x)]
  simp only [L03.localRealBasis_apply]
  have hv : (fun r => chartVec x x (realVec (I r))) =
      ![chartVec x x (realVec (I 0)), chartVec x x (realVec (I 1))] := by
    ext r
    fin_cases r <;> rfl
  rw [hv]
  exact iotaRealForm_represents A hA x _ _

theorem levi_hermitian (f : M.Carrier → ℝ) (hf : SmoothFn f) (x : M.Carrier) :
    (levi f x).IsHermitian :=
  L22Aux.leviC_isHermitian (((hf x).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds (mem_extChartAt_target x))).of_le (by simp))

theorem dd_eq_iota (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    ddRealForm f = iotaRealForm (levi f) (levi_hermitian f hf) := by
  apply L03.realForm_eq_of_center_components
  intro x I
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target x
  rw [dd_coefficients f hf x hz, iotaRealForm_center_components]
  rfl

theorem dd_smooth (f : M.Carrier → ℝ) (hf : SmoothFn f) : SmoothRealForm (ddRealForm f) :=
  L03.smoothRealForm_smul _ _ (L03.exteriorRealForm_smooth _ (jDifferential_smooth f hf))

theorem closedRealForm_smul (c : ℝ) (A : RealForm M k) (hA : SmoothRealForm A)
    (hc : ClosedRealForm A) : ClosedRealForm (c • A) := by
  intro x z hz I
  rw [L03.formComponents_smul, L03.exteriorComponents_smul_at c (formComponents A x) z
    (fun J => ((hA x J).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).differentiableAt (by simp)),
    hc x z hz I, mul_zero]

theorem dd_properties (f : M.Carrier → ℝ) (hf : SmoothFn f) :
    SmoothRealForm (ddRealForm f) ∧ RealOneOne (ddRealForm f) ∧ ClosedRealForm (ddRealForm f) ∧
      RepresentsIota (levi f) (ddRealForm f) := by
  refine ⟨dd_smooth f hf, ?_, ?_, ?_⟩
  · rw [dd_eq_iota f hf]
    exact iotaRealForm_oneOne _ _
  · exact closedRealForm_smul _ _ (L03.exteriorRealForm_smooth _ (jDifferential_smooth f hf))
      (L03.exteriorRealForm_closed _ (jDifferential_smooth f hf))
  · rw [dd_eq_iota f hf]
    exact iotaRealForm_represents _ _

end Yau.NodeProofs.G04Aux
