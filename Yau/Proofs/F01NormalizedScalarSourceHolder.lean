import Yau.Proofs.F01RealHessianContractionCLM
import Yau.Proofs.F01DilatedCoefficientHolder
import Yau.Proofs.F01ParabolicDilation

/-! The actual normalized scalar Ricci forcing has one Holder budget
from the proved principal-symbol bound and the genuine uniform background
log-determinant Hessian jets. No source term is supplied independently. -/
noncomputable section
open Set Metric
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic Yau.LeafProofs.L17Aux
variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

local instance sourceContractionOpNorm (n : ℕ) :
    Norm (Mat n →L[ℝ] (Space n →L[ℝ] Space n →L[ℝ] ℝ) →L[ℝ] ℝ) :=
  ContinuousLinearMap.hasOpNorm

theorem holderBound_real_smul_of_abs_le_one {V : Type*}
    [NormedAddCommGroup V] [NormedSpace ℝ V] {f : Point n → V}
    {Q : Set (Point n)} {β C κ : ℝ} (hf : HolderBound β Q f C) (hκ : |κ| ≤ 1) :
    HolderBound β Q (fun p => κ • f p) C := by
  refine ⟨hf.1, ?_, ?_⟩
  · intro p hp
    rw [norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hκ (hf.2.1 p hp) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)
  · intro p hp q hq
    rw [← smul_sub, norm_smul, Real.norm_eq_abs]
    exact (mul_le_mul hκ (hf.2.2 p hp q hq) (norm_nonneg _) zero_le_one).trans_eq (one_mul _)

theorem normalized_scalar_source_holder_budget (A : BoundedChartFamily g)
    {β Mbound : ℝ} (hβ : β ≤ 1) (hM : 0 ≤ Mbound) :
    ∃ Fbound : ℝ, 0 < Fbound ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ A.radius → ρ ≤ 1 →
      ∀ (a : M.Carrier) (H : Point n → Matrix (Fin n) (Fin n) ℂ),
      HolderBound β (ball 0 1 ×ˢ Icc (-1) 1) (fun p => scalarSymbol (H p)) Mbound →
      HolderBound β (ball 0 1 ×ˢ Icc (-1) 1)
        (fun p => -(ρ ^ 2) * traceWith (H p)
          (backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • p.1))) Fbound := by
  obtain ⟨K, hK, hk⟩ := dilated_spatial_holder_budget
    (A.backgroundLogDet_hessian_uniformJetBounds 1) A.backgroundLogDet_hessian_smooth hβ
  let C0 := 2 * ‖realHessianContractionCLM (n := n)‖ * Mbound * K
  have hC0 : 0 ≤ C0 := mul_nonneg
    (mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2)
      (ContinuousLinearMap.opNorm_nonneg _)) hM) hK.le
  refine ⟨1 + C0, by linarith, ?_⟩
  intro ρ hρ hρr hρ1 a H hH
  have hb := hk ρ hρ hρr hρ1 a
  have hc := holderBound_bilinear hH hb (realHessianContractionCLM (n := n))
  have hρsq : |ρ ^ 2| ≤ 1 := by rw [abs_of_nonneg (sq_nonneg _)]; nlinarith
  have hs := holderBound_real_smul_of_abs_le_one hc hρsq
  have he (p : Point n) (hp : p ∈ ball 0 1 ×ˢ Icc (-1) 1) :
      ρ ^ 2 • realHessianContractionCLM (scalarSymbol (H p)) (backgroundLogDetHessian A a (ρ • p.1)) =
        -(ρ ^ 2) * traceWith (H p) (backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • p.1)) := by
    have hq : ContDiffAt ℝ 2 (A.backgroundLogDet a) (ρ • p.1) :=
      ((A.backgroundLogDet_smooth a).contDiffAt
        (isOpen_ball.mem_nhds (spatialDilation_mem_ball hρ hρr hp.1))).of_le (by simp)
    have hid := native_background_source_contraction (H p) (pullbackMatrix g (A.chart a)) hq
    change -traceWith (H p) (backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • p.1)) =
      realHessianContractionCLM (scalarSymbol (H p)) (backgroundLogDetHessian A a (ρ • p.1)) at hid
    rw [← hid]
    simp only [smul_eq_mul, mul_neg, neg_mul]
  apply holderBound_mono_const (C := C0) (D := 1 + C0) ?_ (by linarith)
  refine ⟨hs.1, ?_, ?_⟩
  · intro p hp
    change ‖-(ρ ^ 2) * traceWith (H p)
      (backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • p.1))‖ ≤ C0
    rw [← he p hp]
    exact hs.2.1 p hp
  · intro p hp q hq
    change ‖-(ρ ^ 2) * traceWith (H p)
        (backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • p.1)) -
      -(ρ ^ 2) * traceWith (H q)
        (backgroundRicci (pullbackMatrix g (A.chart a)) (ρ • q.1))‖ ≤ _
    rw [← he p hp, ← he q hq]
    exact hs.2.2 p hp q hq

end Yau.NodeProofs.F01Aux
