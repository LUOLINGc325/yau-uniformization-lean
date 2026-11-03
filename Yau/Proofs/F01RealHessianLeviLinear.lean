import Yau.Proofs.F01IotaArrayLinear

/-! Exact real-Hessian evaluation packages the native nested Wirtinger
Levi matrix and its realification as continuous real linear maps. -/
noncomputable section
open scoped ContDiff Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

local instance realLeviSymNormedSpace (n : ℕ) : NormedSpace ℝ (Sym n) where
  toModule := inferInstance
  norm_smul_le c A := norm_smul_le c (A : Mat n)

local instance realLeviSymContinuousSMul (n : ℕ) : ContinuousSMul ℝ (Sym n) :=
  (show Topology.IsInducing (fun A : Sym n => (A : Mat n)) from ⟨rfl⟩).continuousSMul
    (f := fun c : ℝ => c) continuous_id (by intros; rfl)

def leviSecondArrayLinear :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) →ₗ[ℝ] ((Fin n × Fin n) → ℂ) where
  toFun B ij :=
    (((B (stdVec ij.2) (stdVec ij.1) +
      B (Complex.I • stdVec ij.2) (Complex.I • stdVec ij.1)) / 4 : ℝ) : ℂ) +
    (((B (stdVec ij.2) (Complex.I • stdVec ij.1) -
      B (Complex.I • stdVec ij.2) (stdVec ij.1)) / 4 : ℝ) : ℂ) * Complex.I
  map_add' B C := by
    funext ij
    apply Complex.ext <;>
      simp [Complex.mul_re, Complex.mul_im] <;> ring
  map_smul' c B := by
    funext ij
    apply Complex.ext <;>
      simp [Algebra.smul_def, Complex.mul_re, Complex.mul_im] <;> ring

def leviSecondArrayCLM :
    (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ((Fin n × Fin n) → ℂ) :=
  LinearMap.toContinuousLinearMap (𝕜 := ℝ)
    (E := Space n →L[ℝ] Space n →L[ℝ] ℝ) (F' := (Fin n × Fin n) → ℂ)
    (leviSecondArrayLinear (n := n))

def realLeviSecondCLM : (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] Sym n :=
  iotaArrayCLM.comp leviSecondArrayCLM

theorem leviSecondArrayCLM_eq_native {q : Space n → ℝ} {z : Space n}
    (hq : ContDiffAt ℝ 2 q z) :
    leviSecondArrayCLM (fderiv ℝ (fderiv ℝ q) z) = fun ij : Fin n × Fin n => leviC q z ij.1 ij.2 := by
  funext ij
  have hre := (LeafProofs.L18Aux.leviMatrix_entry_re_im hq stdVec ij.1 ij.2).1
  have him := (LeafProofs.L18Aux.leviMatrix_entry_re_im hq stdVec ij.1 ij.2).2
  change
    (((((fderiv ℝ (fderiv ℝ q) z) (stdVec ij.2) (stdVec ij.1) +
      (fderiv ℝ (fderiv ℝ q) z) (Complex.I • stdVec ij.2) (Complex.I • stdVec ij.1)) / 4 : ℝ) : ℂ) +
    ((((fderiv ℝ (fderiv ℝ q) z) (stdVec ij.2) (Complex.I • stdVec ij.1) -
      (fderiv ℝ (fderiv ℝ q) z) (Complex.I • stdVec ij.2) (stdVec ij.1)) / 4 : ℝ) : ℂ) * Complex.I) = _
  apply Complex.ext
  · simpa only [
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, sub_zero, add_zero, leviC, one_div, div_eq_mul_inv,
      one_mul, mul_comm] using hre.symm
  · simpa only [
      Complex.add_im, Complex.ofReal_re, Complex.mul_im, Complex.ofReal_im, zero_mul,
      Complex.I_re, Complex.I_im, mul_zero, mul_one, zero_add, add_zero, leviC, one_div, div_eq_mul_inv,
      one_mul, mul_comm] using him.symm

theorem realLeviSecondCLM_eq_native {q : Space n → ℝ} {z : Space n}
    (hq : ContDiffAt ℝ 2 q z) :
    realLeviSecondCLM (fderiv ℝ (fderiv ℝ q) z) = iota (leviC q z) := by
  rw [realLeviSecondCLM, ContinuousLinearMap.comp_apply, leviSecondArrayCLM_eq_native hq]
  rfl

end Yau.NodeProofs.F01Aux
