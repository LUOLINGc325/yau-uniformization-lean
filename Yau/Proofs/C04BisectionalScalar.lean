import Yau.Proofs.C04BisectionalScalarReal

noncomputable section
open scoped Matrix ComplexOrder MatrixOrder
namespace Yau.Proofs.C04BisectionalScalarAux
open Yau Yau.Blueprint Yau.NodeProofs Yau.LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem tensorFrameTransform_four
    {ι κ : Type*} [Fintype ι] [Fintype κ] [DecidableEq ι] [DecidableEq κ]
    (D : Matrix ι κ ℝ) (A : (Fin 4 → ι) → ℝ) (v : Fin 4 → κ) :
    L23Aux.tensorFrameTransform D A v = L23Aux.tensorEvaluation A
      ![fun a => D a (v 0),fun a => D a (v 1),fun a => D a (v 2),fun a => D a (v 3)] := by
  simp only [L23Aux.tensorFrameTransform, L23Aux.tensorEvaluation, L23Aux.tensorProduct,
    Fin.prod_univ_four, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]

/-- The definition's full inverse real metric contraction is controlled by
the scalar using an actual orthonormal Gram factor in every slot. -/
theorem curvatureJetNorm_zero_le (k : HermitianField M) (hs : MetricSmooth k)
    (hk : KahlerClosed k) (hBC : NonnegBisectional k) (x : M.Carrier) :
    curvatureJetNorm k 0 x ≤
      (Fintype.card (Fin 4 → RIdx n) : ℝ)*64*scalarCurvature k x := by
  let G := realMetricFn k x (chartPt x x)
  let A := rmTensor k x (chartPt x x)
  obtain ⟨D,hD,hGram⟩ := L23Aux.inverseMetric_exists_orthonormal_factor G
    (L12Aux.realMetricFn_posDef k x _ (mem_extChartAt_target x))
  let E : RIdx n → ComplexVector n := fun i => ∑ a, D a i • realVec a
  have he (i : RIdx n) : realCoord (E i) = fun a => D a i :=
    funext (L12Aux.realCoord_sum_realVec (fun a => D a i))
  have hcol (i : RIdx n) :
      (fun a => D a i) ⬝ᵥ (G *ᵥ (fun a => D a i)) = 1 := by
    rw [Matrix.mul_assoc] at hGram
    have hh := congrArg (fun B : Matrix (RIdx n) (RIdx n) ℝ => B i i) hGram
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,
      dotProduct,Matrix.mulVec] using hh
  have hunit (i : RIdx n) : metricQuadratic (gMat k x) (fun a => E i a) ≤ 1 := by
    have hh := metricQuadratic_real_coords k x (E i)
    rw [he] at hh
    change 2*metricQuadratic (gMat k x) (fun a => E i a) =
      (fun a => D a i) ⬝ᵥ (G *ᵥ (fun a => D a i)) at hh
    rw [hcol] at hh
    linarith
  have hframe (v : Fin 4 → RIdx n) :
      |L23Aux.tensorFrameTransform D A v| ≤ 64*scalarCurvature k x := by
    rw [tensorFrameTransform_four, ← he (v 0), ← he (v 1), ← he (v 2), ← he (v 3)]
    change |L23Aux.tensorEvaluation (rmTensor k x (chartPt x x))
      ![realCoord (E (v 0)),realCoord (E (v 1)),realCoord (E (v 2)),realCoord (E (v 3))]| ≤ _
    rw [tensorEvaluation_rm_eq]
    exact realRm_unit_bound k hs hk hBC x _ _ _ _
      (hunit (v 0)) (hunit (v 1)) (hunit (v 2)) (hunit (v 3))
  have hsq : covTensorNormSq G A =
      ∑ v : Fin 4 → RIdx n, (L23Aux.tensorFrameTransform D A v)^2 := by
    unfold covTensorNormSq
    rw [L23Aux.tensor_contraction_eq_frame_sum _ D hD]
    simp only [pow_two]
  have hnorm : curvatureJetNorm k 0 x ≤
      ∑ v : Fin 4 → RIdx n, |L23Aux.tensorFrameTransform D A v| := by
    change Real.sqrt (covTensorNormSq G A) ≤ _
    rw [hsq]
    apply Real.sqrt_le_iff.mpr
    refine ⟨Finset.sum_nonneg (fun v _ => abs_nonneg _), ?_⟩
    simpa only [sq_abs] using Finset.sum_sq_le_sq_sum_of_nonneg
      (s := Finset.univ) (f := fun v : Fin 4 → RIdx n => |L23Aux.tensorFrameTransform D A v|)
      (fun v _ => abs_nonneg _)
  calc
    curvatureJetNorm k 0 x ≤ _ := hnorm
    _ ≤ ∑ v : Fin 4 → RIdx n, 64*scalarCurvature k x :=
      Finset.sum_le_sum (fun v _ => hframe v)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul]; ring

theorem pointwise_bounds : ∀ n : ℕ, ∃ Cn : ℝ, 0 < Cn ∧
    ∀ (M : ComplexManifold n) (k : HermitianField M),
      MetricSmooth k → KahlerClosed k → NonnegBisectional k → ∀ x,
      (ricci k x).PosSemidef ∧ 0 ≤ scalarCurvature k x ∧
      HermLE (ricci k x) (((scalarCurvature k x : ℝ) : ℂ) • gMat k x) ∧
      curvatureJetNorm k 0 x ≤ Cn*scalarCurvature k x := by
  intro n
  refine ⟨64*((Fintype.card (Fin 4 → RIdx n) : ℝ)+1), by positivity, ?_⟩
  intro M k hs hk hBC x
  obtain ⟨hRic,hR,hupper⟩ := ricci_scalar_bounds k hs hk hBC x
  refine ⟨hRic,hR,hupper,?_⟩
  have hh := curvatureJetNorm_zero_le k hs hk hBC x
  nlinarith

end Yau.Proofs.C04BisectionalScalarAux
