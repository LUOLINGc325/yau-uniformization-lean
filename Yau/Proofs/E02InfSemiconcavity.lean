import Yau.Proofs.E02InfConvolution

open Set Filter
open scoped Topology InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

theorem inf_cost_sub_quadratic_affine (v : E → ℝ) (κ : ℝ) (q s : E) :
    v s+‖q-s‖^2/(2*κ)-‖q‖^2/(2*κ) =
      v s+‖s‖^2/(2*κ)-⟪q,s⟫_ℝ/κ := by
  rw [norm_sub_sq_real]
  ring

/-- Subtracting the fixed quadratic from the actual attained compact
infimum is concave on all real Euclidean space. -/
theorem compactInfConvolution_sub_quadratic_concave
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ s ∈ K, 0 ≤ v s)
    {κ : ℝ} (hκ : 0 < κ) :
    ConcaveOn ℝ univ (fun q => compactInfConvolution K v κ q-‖q‖^2/(2*κ)) := by
  refine ⟨convex_univ,?_⟩
  intro x _ y _ a b ha hb hab
  obtain ⟨s,hs,hEq,_⟩ := compactInfConvolution_attained K v hK hne hv κ (a • x+b • y)
  have hx : compactInfConvolution K v κ x-‖x‖^2/(2*κ) ≤
      v s+‖s‖^2/(2*κ)-⟪x,s⟫_ℝ/κ := by
    rw [←inf_cost_sub_quadratic_affine v κ x s]
    linarith [compactInfConvolution_le_cost K v hv0 hκ x s hs]
  have hy : compactInfConvolution K v κ y-‖y‖^2/(2*κ) ≤
      v s+‖s‖^2/(2*κ)-⟪y,s⟫_ℝ/κ := by
    rw [←inf_cost_sub_quadratic_affine v κ y s]
    linarith [compactInfConvolution_le_cost K v hv0 hκ y s hs]
  have hLin : v s+‖s‖^2/(2*κ)-⟪a • x+b • y,s⟫_ℝ/κ =
      a*(v s+‖s‖^2/(2*κ)-⟪x,s⟫_ℝ/κ)+
      b*(v s+‖s‖^2/(2*κ)-⟪y,s⟫_ℝ/κ) := by
    rw [inner_add_left,real_inner_smul_left,real_inner_smul_left]
    have hC : (a+b)*(v s+‖s‖^2/(2*κ)) = v s+‖s‖^2/(2*κ) := by rw [hab,one_mul]
    linear_combination -hC
  simp only [smul_eq_mul]
  rw [hEq,inf_cost_sub_quadratic_affine,hLin]
  exact add_le_add (mul_le_mul_of_nonneg_left hx ha) (mul_le_mul_of_nonneg_left hy hb)

theorem compactInfConvolution_continuous [FiniteDimensional ℝ E]
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hne : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ s ∈ K, 0 ≤ v s)
    {κ : ℝ} (hκ : 0 < κ) : Continuous (compactInfConvolution K v κ) := by
  have hConc := compactInfConvolution_sub_quadratic_concave K v hK hne hv hv0 hκ
  have hC : Continuous (fun q => compactInfConvolution K v κ q-‖q‖^2/(2*κ)) :=
    continuousOn_univ.mp (hConc.continuousOn isOpen_univ)
  have hQ : Continuous (fun q : E => ‖q‖^2/(2*κ)) := by fun_prop
  convert hC.add hQ using 1
  funext q
  simp only [Pi.add_apply]
  ring

end Yau.NodeProofs.E02Aux
