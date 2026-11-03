import Yau.LeafProofs.L23DistanceEnergyPhysicalTrace

/-! The true second-variation trace has the dimension-curvature bound. -/

noncomputable section
open scoped Topology ContDiff Manifold
namespace Yau.LeafProofs.L23Aux
open L12Aux
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

variable {n : ℕ} {M : ComplexManifold n}

theorem connectionCurvature_smul_first_third
    (Γ : ComplexVector n → ComplexVector n →L[ℝ] ComplexVector n →L[ℝ] ComplexVector n)
    (z V T : ComplexVector n) (u : ℝ) :
    connectionCurvature Γ z (u • V) T (u • V)=u^2 • connectionCurvature Γ z V T V := by
  simp only [←connectionCurvatureMap_apply,map_smul,smul_apply,smul_smul,pow_two]

theorem secondEnergyDensity_orthonormal_trace_le
    (h : HermitianField M) (hh : MetricSmooth h) (x : M.Carrier) (T : ComplexVector n)
    (u K d : ℝ) (hK : curvatureJetNorm h 0 x≤K)
    (hspeed : realMetricInChart h x (chartPt x x) T T=d^2)
    (b : letI := underlyingRealTangentNormedAddCommGroup h x
      letI := underlyingRealTangentInnerProductSpace h x
      OrthonormalBasis (Fin (2*n)) ℝ (TangentSpace 𝓘(ℝ, ComplexVector n) x)) :
    (∑ i : Fin (2*n), (2*realMetricInChart h x (chartPt x x) (realTangentCoords x x (b i)) (realTangentCoords x x (b i))+
      2*realMetricInChart h x (chartPt x x) T
        (connectionCurvature (chartChristoffelBilin h x) (chartPt x x)
          (u • realTangentCoords x x (b i)) T (u • realTangentCoords x x (b i)))))≤
        2*(2*n : ℕ)+2*u^2*(2*n : ℕ)*K*d^2 := by
  letI := underlyingRealTangentNormedAddCommGroup h x
  letI := underlyingRealTangentInnerProductSpace h x
  let R := ∑ j, ∑ l, realRicciCoeff h x (chartPt x x) j l*realCoord T j*realCoord T l
  have hNorm (i : Fin (2*n)) : realMetricInChart h x (chartPt x x)
      (realTangentCoords x x (b i)) (realTangentCoords x x (b i))=1 := by
    rw [realMetricInChart_tangentCoords h x x (mem_chart_source _ _)]
    exact b.inner_eq_one i
  have hTrace : (∑ i, realMetricInChart h x (chartPt x x) T
      (connectionCurvature (chartChristoffelBilin h x) (chartPt x x)
        (realTangentCoords x x (b i)) T (realTangentCoords x x (b i))))=-R := by
    simp only [realMetricInChart_symm h x (chartPt x x) T]
    exact connectionCurvature_orthonormal_trace h hh x T b
  have hR : |R|≤(2*n : ℕ)*K*d^2 := by
    have hinv : chartInv x (chartPt x x)=x :=
      (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
    have hK' : curvatureJetNorm h 0 (chartInv x (chartPt x x))≤K := by rw [hinv]; exact hK
    have H := realRicciCoeff_quadratic_abs_le_of_curvatureBound h hh x
      (z := chartPt x x) (mem_extChartAt_target x) T K hK'
    rw [hspeed] at H
    exact H
  have hRlo : -R≤(2*n : ℕ)*K*d^2 := by
    have H := (abs_le.mp hR).1
    linarith
  calc
    _=2*(2*n : ℕ)-2*u^2*R := by
      simp only [connectionCurvature_smul_first_third,map_smul,smul_eq_mul,hNorm]
      rw [Finset.sum_add_distrib]
      have he : (∑ i : Fin (2*n),2*(u^2*realMetricInChart h x (chartPt x x) T
          (connectionCurvature (chartChristoffelBilin h x) (chartPt x x)
            (realTangentCoords x x (b i)) T (realTangentCoords x x (b i)))))=
          2*u^2*∑ i : Fin (2*n), realMetricInChart h x (chartPt x x) T
          (connectionCurvature (chartChristoffelBilin h x) (chartPt x x)
            (realTangentCoords x x (b i)) T (realTangentCoords x x (b i))) := by
        simp only [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        ring
      rw [he,hTrace]
      simp only [mul_one,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul]
      ring
    _≤_ := by nlinarith [mul_le_mul_of_nonneg_left hRlo (show 0≤2*u^2 by positivity)]

end Yau.LeafProofs.L23Aux
