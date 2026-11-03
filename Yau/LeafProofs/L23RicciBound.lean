import Yau.LeafProofs.L23TensorEvaluation

/-! The Ricci contraction is bounded by the full, actual curvature norm. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux

section Finite
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

theorem sum_tensor_cons {r : ℕ} (f : (Fin (r+1) → ι) → ℝ) :
    (∑ v, f v) = ∑ a : ι, ∑ v : Fin r → ι, f (Fin.cons a v) := by
  calc
    _ = ∑ q : ι × (Fin r → ι), f (Fin.cons q.1 q.2) :=
      ((Fin.consEquiv (fun _ : Fin (r+1) => ι)).sum_comp f).symm
    _ = _ := Fintype.sum_prod_type _

theorem tensorEvaluation_four (A : (Fin 4 → ι) → ℝ) (V₀ V₁ V₂ V₃ : ι → ℝ) :
    tensorEvaluation A ![V₀,V₁,V₂,V₃] =
      ∑ a, ∑ b, ∑ c, ∑ d, A ![a,b,c,d]*V₀ a*V₁ b*V₂ c*V₃ d := by
  simp [tensorEvaluation, tensorProduct, sum_tensor_cons, Fin.prod_univ_succ, mul_assoc]
  rfl

theorem inverseMetric_exists_orthonormal_factor (G : Matrix ι ι ℝ) (hG : G.PosDef) :
    ∃ D : Matrix ι ι ℝ, G⁻¹ = D*Dᵀ ∧ Dᵀ*G*D=1 := by
  obtain ⟨D,hD⟩ := inverseMetric_exists_gram_factor G hG
  have hdet : D.det ≠ 0 := by
    intro hz
    have hh := congrArg Matrix.det hD
    rw [Matrix.det_mul, Matrix.det_transpose, hz, zero_mul] at hh
    exact hG.inv.det_pos.ne' hh
  have hInvD : D⁻¹*D=1 := Matrix.nonsing_inv_mul D (isUnit_iff_ne_zero.mpr hdet)
  have hInvG : G⁻¹*G=1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr hG.det_pos.ne')
  refine ⟨D,hD,?_⟩
  calc
    Dᵀ*G*D = (D⁻¹*D)*Dᵀ*G*D := by rw [hInvD,Matrix.one_mul]
    _ = D⁻¹*(D*Dᵀ)*G*D := by simp only [Matrix.mul_assoc]
    _ = D⁻¹*(G⁻¹*G)*D := by rw [←hD]; simp only [Matrix.mul_assoc]
    _ = 1 := by rw [hInvG,Matrix.mul_one,hInvD]

theorem five_sum_trace_reorder (f : ι → ι → ι → ι → ι → ℝ) :
    (∑ i, ∑ a, ∑ j, ∑ k, ∑ b, f i a j k b) =
      ∑ j, ∑ k, ∑ a, ∑ b, ∑ i, f i a j k b := by
  calc
    _ = ∑ a, ∑ j, ∑ k, ∑ b, ∑ i, f i a j k b := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro a _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k _
      exact Finset.sum_comm
    _ = _ := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_comm]

end Finite

variable {n : ℕ}

theorem curvature_contraction_abs_le (G : Matrix (RIdx n) (RIdx n) ℝ)
    (hG : G.PosDef) (A : CovTensor n 4) (V : RIdx n → ℝ) :
    |∑ j, ∑ k, (∑ a, ∑ b, G⁻¹ a b*A ![a,j,k,b])*V j*V k| ≤
      (Fintype.card (RIdx n) : ℝ)*Real.sqrt (covTensorNormSq G A)*(V ⬝ᵥ (G *ᵥ V)) := by
  obtain ⟨D,hD,hGram⟩ := inverseMetric_exists_orthonormal_factor G hG
  let e : RIdx n → RIdx n → ℝ := fun i a => D a i
  let Q := V ⬝ᵥ (G *ᵥ V)
  let N := covTensorNormSq G A
  have hQ : 0 ≤ Q := by
    simpa only [Q,star_trivial] using hG.posSemidef.dotProduct_mulVec_nonneg V
  have hN : 0 ≤ N := covTensorNormSq_nonneg G hG A
  have hcol (i : RIdx n) : e i ⬝ᵥ (G *ᵥ e i) = 1 := by
    rw [Matrix.mul_assoc] at hGram
    have hh := congrArg (fun H : Matrix (RIdx n) (RIdx n) ℝ => H i i) hGram
    simpa only [Matrix.mul_apply,Matrix.transpose_apply,Matrix.one_apply_eq,
      dotProduct,Matrix.mulVec,e] using hh
  have heval (i : RIdx n) :
      |tensorEvaluation A ![e i,V,V,e i]| ≤ Real.sqrt N*Q := by
    have hh := tensorEvaluation_sq_le G hG A ![e i,V,V,e i]
    have hprod : (∏ j : Fin 4,
        ![e i,V,V,e i] j ⬝ᵥ (G *ᵥ ![e i,V,V,e i] j)) = Q^2 := by
      simp [Fin.prod_univ_succ,hcol,Q,pow_two]
    rw [hprod] at hh
    have hs := Real.sq_sqrt hN
    have hpos : 0 ≤ Real.sqrt N*Q := mul_nonneg (Real.sqrt_nonneg _) hQ
    apply abs_le.mpr
    constructor <;> nlinarith
  have htrace : (∑ j, ∑ k, (∑ a, ∑ b, G⁻¹ a b*A ![a,j,k,b])*V j*V k) =
      ∑ i, tensorEvaluation A ![e i,V,V,e i] := by
    simp only [tensorEvaluation_four]
    rw [five_sum_trace_reorder]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro k _
    simp only [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro a _
    apply Finset.sum_congr rfl
    intro b _
    have hrow := congrArg (fun H : Matrix (RIdx n) (RIdx n) ℝ => H a b) hD
    simp only [Matrix.mul_apply,Matrix.transpose_apply] at hrow
    rw [hrow]
    simp only [Finset.sum_mul,e]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [htrace]
  calc
    |∑ i, tensorEvaluation A ![e i,V,V,e i]| ≤
        ∑ i, |tensorEvaluation A ![e i,V,V,e i]| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : RIdx n, Real.sqrt N*Q := Finset.sum_le_sum (fun i _ => heval i)
    _ = _ := by simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,N,Q]; ring

variable {M : ComplexManifold n}

theorem realRicciCoeff_eq_realRicciMatrix (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (j k : RIdx n) :
    realRicciCoeff h x z j k=L12Aux.realRicciMatrix h x z j k := by
  let G := realMetricFn h x z
  have hsym : Gᵀ=G := L18Aux.realMetricFn_isSymm h x z
  have hInv : G⁻¹*G=1 := Matrix.nonsing_inv_mul G
    (isUnit_iff_ne_zero.mpr (L12Aux.realMetricFn_posDef h x z hz).det_pos.ne')
  unfold realRicciCoeff L12Aux.realRicciMatrix
  apply Finset.sum_congr rfl
  intro a _
  let V : RIdx n → ℝ := fun l => riemannCoeff h x z a j k l
  change (G⁻¹ *ᵥ (Gᵀ *ᵥ V)) a=V a
  rw [hsym,Matrix.mulVec_mulVec,hInv,Matrix.one_mulVec]

theorem realRicciCoeff_quadratic_abs_le (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) (hz : z ∈ chartTarget x) (V : RIdx n → ℝ) :
    |∑ j, ∑ k, realRicciCoeff h x z j k*V j*V k| ≤
      (2*n : ℕ)*Real.sqrt (covTensorNormSq (realMetricFn h x z) (rmTensor h x z))*
        (V ⬝ᵥ (realMetricFn h x z *ᵥ V)) := by
  have hh := curvature_contraction_abs_le (realMetricFn h x z)
    (L12Aux.realMetricFn_posDef h x z hz) (rmTensor h x z) V
  simpa [realRicciCoeff,rmTensor,
    Fintype.card_prod,Fintype.card_fin,mul_comm (n : ℕ) 2] using hh

theorem realRicciQuadratic_abs_le (h : HermitianField M) (x : M.Carrier)
    (v : TangentVector M x) :
    |∑ i, ∑ j, realRicciCoeff h x (chartPt x x) i j *
      realCoord (tangentCoords x x v) i * realCoord (tangentCoords x x v) j| ≤
      (2*n : ℕ)*curvatureJetNorm h 0 x*(2*hermitianNormSq (h x) v) := by
  let V := realCoord (tangentCoords x x v)
  have hQ : V ⬝ᵥ (realMetricFn h x (chartPt x x) *ᵥ V) =
      2*hermitianNormSq (h x) v := by
    rw [←L12Aux.realMetricTensor_quadratic]
    simp only [dotProduct,Matrix.mulVec,Finset.mul_sum,V,mul_left_comm,mul_assoc]
  have hh := realRicciCoeff_quadratic_abs_le h x (chartPt x x)
    (mem_extChartAt_target x) V
  simpa only [hQ,curvatureJetNorm,rmJet,V] using hh

end Yau.LeafProofs.L23Aux
