import Yau.LeafProofs.L17AffineLogDetDerivative
import Yau.LeafProofs.L17BanachRadialLogarithm
import Mathlib.Analysis.Normed.Module.FiniteDimension

open Set Metric
open scoped Matrix.Norms.Frobenius ComplexOrder
noncomputable section
set_option maxHeartbeats 1400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17Aux
open L17BanachLogarithmAux L17BanachRadialLogarithmAux
local instance logDetMatrixGroup (n : ℕ) : NormedAddCommGroup (Matrix (Fin n) (Fin n) ℂ) :=
  @NonUnitalNormedRing.toNormedAddCommGroup _ (@NormedRing.toNonUnitalNormedRing _ (Matrix.frobeniusNormedRing : NormedRing (Matrix (Fin n) (Fin n) ℂ)))
local instance logDetMatrixSpace (n : ℕ) : NormedSpace ℝ (Matrix (Fin n) (Fin n) ℂ) :=
  (Matrix.frobeniusNormedAlgebra : NormedAlgebra ℝ (Matrix (Fin n) (Fin n) ℂ)).toNormedSpace
local instance logDetMatrixTopology (n : ℕ) : TopologicalSpace (Matrix (Fin n) (Fin n) ℂ) :=
  (Matrix.frobeniusNormedRing : NormedRing (Matrix (Fin n) (Fin n) ℂ)).toUniformSpace.toTopologicalSpace

local instance logDetMatrixComplete (n : ℕ) : CompleteSpace (Matrix (Fin n) (Fin n) ℂ) :=
  FiniteDimensional.complete ℝ (Matrix (Fin n) (Fin n) ℂ)

def logDetRealTraceLinearMap (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] ℝ where
  toFun H := (Matrix.trace H).re
  map_add' H K := by simp only [Matrix.trace_add,Complex.add_re]
  map_smul' c H := by
    simp only [Matrix.trace_smul,RingHom.id_apply,Complex.smul_re,smul_eq_mul]

def logDetRealTraceCLM (n : ℕ) : Matrix (Fin n) (Fin n) ℂ →L[ℝ] ℝ :=
  {logDetRealTraceLinearMap n with cont := (logDetRealTraceLinearMap n).continuous_of_finiteDimensional}

theorem realTrace_log_radial_hasDerivAt {n : ℕ} (Z : Matrix (Fin n) (Fin n) ℂ)
    (hZ : ‖Z‖<1) {s : ℝ} (hs : |s|≤1) :
    HasDerivAt (fun t : ℝ => (Matrix.trace (logIncrement _ (t • Z))).re)
      (Matrix.trace (radialLogDerivative _ Z s)).re s :=
  (logDetRealTraceCLM n).hasFDerivAt.comp_hasDerivAt s
    (radialLogDerivative_hasDerivAt _ hZ hs)


theorem affine_posDef_of_endpoints {n : ℕ} (G E : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.PosDef) (hE : (G+E).PosDef) {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    (G+s • E).PosDef := by
  by_cases hOne : s=1
  · simpa only [hOne,one_smul] using hE
  have hs1 : s<1 := lt_of_le_of_ne hs.2 hOne
  have h := (hG.smul (sub_pos.mpr hs1)).add_posSemidef (hE.posSemidef.smul hs.1)
  convert h using 1
  module

theorem radialLogDerivative_normalized {n : ℕ} (G E : Matrix (Fin n) (Fin n) ℂ)
    (hG : G.PosDef) (hE : (G+E).PosDef) (hZ : ‖G⁻¹*E‖<1)
    {s : ℝ} (hs : s∈Icc (0:ℝ) 1) :
    radialLogDerivative _ (G⁻¹*E) s=(G+s • E)⁻¹*E := by
  have hGunit : IsUnit G.det := isUnit_iff_ne_zero.mpr hG.det_pos.ne'
  have hAunit : IsUnit (G+s • E).det :=
    isUnit_iff_ne_zero.mpr (affine_posDef_of_endpoints G E hG hE hs).det_pos.ne'
  have hFactor : G*(1+s • (G⁻¹*E))=G+s • E := by
    rw [Matrix.mul_add,Matrix.mul_one,Matrix.mul_smul,←Matrix.mul_assoc,Matrix.mul_nonsing_inv G hGunit,Matrix.one_mul]
  have hB : ((G+s • E)⁻¹*G)*(1+s • (G⁻¹*E))=1 := by
    rw [Matrix.mul_assoc,hFactor,Matrix.nonsing_inv_mul _ hAunit]
  rw [radialLogDerivative_eq_mul_of_left_inverse _ hZ (abs_le.mpr ⟨by linarith [hs.1],hs.2⟩) _ hB]
  rw [Matrix.mul_assoc,←Matrix.mul_assoc G,Matrix.mul_nonsing_inv G hGunit,Matrix.one_mul]


theorem matrixTraceLogIncrement_eq_logdet_ratio {n : ℕ}
    (G E : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) (hE : (G+E).PosDef)
    (hZ : ‖G⁻¹*E‖<1) :
    (Matrix.trace (logIncrement _ (G⁻¹*E))).re=
      Real.log ((G+E).det.re/G.det.re) := by
  let F : ℝ → ℝ := fun s =>
    (Matrix.trace (logIncrement _ (s • (G⁻¹*E)))).re-
      (Real.log (G+s • E).det.re-Real.log G.det.re)
  have hD (s : ℝ) (hs : s∈Icc (0:ℝ) 1) : HasDerivAt F 0 s := by
    have hLog := realTrace_log_radial_hasDerivAt (G⁻¹*E) hZ
      (abs_le.mpr ⟨by linarith [hs.1],hs.2⟩)
    rw [radialLogDerivative_normalized G E hG hE hZ hs] at hLog
    have hDet := (affine_logDet_hasDerivAt G E s
      (affine_posDef_of_endpoints G E hG hE hs)).sub_const (Real.log G.det.re)
    convert! hLog.sub hDet using 1
    simp only [sub_self]
  have hBound := (convex_Icc (0:ℝ) 1).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s hs => (hD s hs).hasDerivWithinAt)
    (fun s (_ : s∈Icc (0:ℝ) 1) => le_refl ‖(0:ℝ)‖)
    (show (0:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
    (show (1:ℝ)∈Icc (0:ℝ) 1 by constructor <;> norm_num)
  have he : F 1=F 0 := sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (by simpa only [norm_zero,zero_mul] using hBound) (norm_nonneg _)))
  have hGdet : G.det.re≠0 := (Complex.pos_iff.mp hG.det_pos).1.ne'
  have hEdet : (G+E).det.re≠0 := (Complex.pos_iff.mp hE.det_pos).1.ne'
  rw [Real.log_div hEdet hGdet]
  have he0 : F 0=0 := by
    simp only [F,zero_smul,logIncrement_zero,Matrix.trace_zero,Complex.zero_re,add_zero,sub_self]
  have he1 : F 1=0 := he.trans he0
  apply sub_eq_zero.mp
  simpa only [F,one_smul] using he1

end Yau.LeafProofs.L17Aux
