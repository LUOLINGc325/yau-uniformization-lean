import Yau.Proofs.G04LeviForms

noncomputable section
open scoped Topology ContDiff Matrix
open Filter
namespace Yau.NodeProofs.G04Aux
open Yau Yau.LeafProofs
set_option backward.isDefEq.respectTransparency false
variable {n k : ℕ}

def modelOneForm (L : ComplexVector n →L[ℝ] ℝ) : (ComplexVector n) [⋀^Fin 1]→L[ℝ] ℝ where
  toContinuousMultilinearMap := (continuousMultilinearCurryFin1 ℝ (ComplexVector n) ℝ).symm L
  map_eq_zero_of_eq' _ i j _ hij := False.elim (hij (Subsingleton.elim i j))

theorem modelOneForm_apply (L : ComplexVector n →L[ℝ] ℝ) (V : Fin 1 → ComplexVector n) :
    modelOneForm L V = L (V 0) := rfl

def modelJd (q : ComplexVector n → ℝ) (z : ComplexVector n) :
    (ComplexVector n) [⋀^Fin 1]→L[ℝ] ℝ :=
  modelOneForm ((fderiv ℝ q z).comp (L12Aux.complexStructureCLM n))

theorem modelJd_coeff (q : ComplexVector n → ℝ) (z : ComplexVector n) (I : Fin 1 → RIdx n) :
    modelJd q z (fun r => realVec (I r)) = jScalarComponents q z I := by
  change fderiv ℝ q z (Complex.I • realVec (I 0)) = _
  rw [I_smul_realVec, map_smul]
  rfl

theorem modelJd_smooth (q : ComplexVector n → ℝ) {O : Set (ComplexVector n)}
    (hO : IsOpen O) (hq : ContDiffOn ℝ ∞ q O) : ContDiffOn ℝ ∞ (modelJd q) O := by
  apply (L03.modelForm_contDiffOn_iff _ _).mpr
  intro I
  simpa only [modelJd_coeff, jScalarComponents] using
    (contDiffOn_const.mul (L12Aux.rDeriv_contDiffOn hO hq (L12Aux.jIndex n (I 0))))

theorem model_extDeriv_coeff (F : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    {z : ComplexVector n} (hF : DifferentiableAt ℝ F z) (I : Fin (k + 1) → RIdx n) :
    extDeriv F z (fun r => realVec (I r)) =
      exteriorComponents (fun w J => F w (fun r => realVec (J r))) z I := by
  rw [extDeriv_apply hF]
  simp only [exteriorComponents]
  apply Finset.sum_congr rfl
  intro r _
  have heq : (fun w => F w (r.removeNth (fun s => realVec (I s)))) =
      (fun w => F w (fun s => realVec (I (r.succAbove s)))) := by
    funext w
    rfl
  rw [heq]
  simp [rDeriv, zsmul_eq_mul]

theorem model_extDeriv_smooth (F : ComplexVector n → (ComplexVector n) [⋀^Fin k]→L[ℝ] ℝ)
    {O : Set (ComplexVector n)} (hO : IsOpen O) (hF : ContDiffOn ℝ ∞ F O) :
    ContDiffOn ℝ ∞ (extDeriv F) O := by
  have hd : ContDiffOn ℝ ∞ (fderiv ℝ F) O := hF.fderiv_of_isOpen hO (by simp)
  change ContDiffOn ℝ ∞
    (fun z => ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ (ComplexVector n) ℝ
      (fderiv ℝ F z)) O
  exact (ContinuousAlternatingMap.alternatizeUncurryFinCLM (n := k) ℝ (ComplexVector n) ℝ).contDiff.comp_contDiffOn hd

def modelDd (q : ComplexVector n → ℝ) : ComplexVector n → (ComplexVector n) [⋀^Fin 2]→L[ℝ] ℝ :=
  fun z => -(1 / 2 : ℝ) • extDeriv (modelJd q) z

theorem modelDd_smooth (q : ComplexVector n → ℝ) {O : Set (ComplexVector n)}
    (hO : IsOpen O) (hq : ContDiffOn ℝ ∞ q O) : ContDiffOn ℝ ∞ (modelDd q) O :=
  (model_extDeriv_smooth _ hO (modelJd_smooth q hO hq)).const_smul (-(1 / 2 : ℝ))

theorem modelDd_coeff (q : ComplexVector n → ℝ) {O : Set (ComplexVector n)}
    (hO : IsOpen O) (hq : ContDiffOn ℝ ∞ q O) {z : ComplexVector n} (hz : z ∈ O)
    (I : Fin 2 → RIdx n) :
    modelDd q z (fun r => realVec (I r)) =
      2 * (matrixPairing (leviC q z) (realVec (I 0)) (realVec (I 1))).im := by
  have hF := ((modelJd_smooth q hO hq).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp)
  simp only [modelDd, ContinuousAlternatingMap.smul_apply, smul_eq_mul]
  rw [model_extDeriv_coeff _ hF]
  simp only [modelJd_coeff]
  exact local_dd_levi ((hq.contDiffAt (hO.mem_nhds hz)).of_le (by simp)) I

theorem localLevi_coeff_smooth (q : ComplexVector n → ℝ) {O : Set (ComplexVector n)}
    (hO : IsOpen O) (hq : ContDiffOn ℝ ∞ q O) (I : Fin 2 → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => 2 * (matrixPairing (leviC q z)
      (realVec (I 0)) (realVec (I 1))).im) O := by
  apply ((ContinuousAlternatingMap.apply ℝ (ComplexVector n) ℝ (fun r => realVec (I r))).contDiff.comp_contDiffOn
    (modelDd_smooth q hO hq)).congr
  intro z hz
  exact (modelDd_coeff q hO hq hz I).symm

theorem localLevi_coeff_closed (q : ComplexVector n → ℝ) {O : Set (ComplexVector n)}
    (hO : IsOpen O) (hq : ContDiffOn ℝ ∞ q O) {z : ComplexVector n} (hz : z ∈ O)
    (I : Fin 3 → RIdx n) :
    exteriorComponents (fun w J => 2 * (matrixPairing (leviC q w)
      (realVec (J 0)) (realVec (J 1))).im) z I = 0 := by
  have heq : (fun w (J : Fin 2 → RIdx n) => 2 * (matrixPairing (leviC q w)
      (realVec (J 0)) (realVec (J 1))).im) =ᶠ[𝓝 z]
      (fun w (J : Fin 2 → RIdx n) => modelDd q w (fun r => realVec (J r))) := by
    filter_upwards [hO.mem_nhds hz] with w hw
    funext J
    exact (modelDd_coeff q hO hq hw J).symm
  rw [congrFun (L03.exteriorComponents_congr_nhds heq) I,
    ← model_extDeriv_coeff _ (((modelDd_smooth q hO hq).contDiffAt (hO.mem_nhds hz)).differentiableAt (by simp))]
  have hd : extDeriv (modelDd q) z = 0 := by
    change extDeriv ((-(1 / 2 : ℝ)) • extDeriv (modelJd q)) z = 0
    rw [extDeriv_smul, extDeriv_extDeriv_apply
      ((modelJd_smooth q hO hq).contDiffAt (hO.mem_nhds hz)) (by simp), smul_zero]
  rw [hd]
  rfl

end Yau.NodeProofs.G04Aux
