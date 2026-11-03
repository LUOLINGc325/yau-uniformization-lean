import Yau.Proofs.E02InfSemiconcavity
import Yau.Proofs.E02HessianConvex

open Set Filter
open scoped Topology ContDiff InnerProductSpace
noncomputable section
namespace Yau.NodeProofs.E02Aux

variable {D E : Type*} [NormedAddCommGroup D] [InnerProductSpace ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The Euclidean projection contraction supplies a positive quadratic
surplus, using the true Hessian of the two squared norms. -/
theorem contraction_quadratic_convex (L : D →L[ℝ] E) (hL : ∀ v, ‖L v‖ ≤ ‖v‖)
    {κ : ℝ} (hκ : 0 < κ) :
    ConvexOn ℝ univ (fun x => ‖x‖^2/(2*κ)-‖L x‖^2/(2*κ)) := by
  have hD : ContDiff ℝ 2 (fun x : D => ‖x‖^2/(2*κ)-‖L x‖^2/(2*κ)) :=
    ((contDiff_norm_sq ℝ).div_const _).sub ((L.contDiff.norm_sq ℝ).div_const _)
  apply convexOn_univ_of_second_fderiv_nonneg _ hD
  intro x v
  have hJet := realSecondJet_sub (realSecondJet_norm_sq_div_two κ x)
    (realSecondJet_comp_continuousLinearMap L (realSecondJet_norm_sq_div_two κ (L x)))
  rw [realSecondJet_second_fderiv_eq hJet hD.contDiffAt]
  change 0 ≤ κ⁻¹*⟪v,v⟫_ℝ-κ⁻¹*⟪L v,L v⟫_ℝ
  rw [real_inner_self_eq_norm_sq,real_inner_self_eq_norm_sq,←mul_sub]
  apply mul_nonneg (inv_nonneg.mpr hκ.le)
  exact sub_nonneg.mpr ((sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mpr (hL v))

/-- Each projected actual inf-convolution has the same global
semiconcavity modulus, because the fixed real projection is a contraction. -/
theorem projected_compactInfConvolution_quadratic_convex
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hNE : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ s ∈ K, 0 ≤ v s)
    (L : D →L[ℝ] E) (hL : ∀ w, ‖L w‖ ≤ ‖w‖) {κ : ℝ} (hκ : 0 < κ) :
    ConvexOn ℝ univ (fun x => ‖x‖^2/(2*κ)-compactInfConvolution K v κ (L x)) := by
  have hC := (compactInfConvolution_sub_quadratic_concave K v hK hNE hv hv0 hκ).neg
  have hComp : ConvexOn ℝ univ
      (fun x => ‖L x‖^2/(2*κ)-compactInfConvolution K v κ (L x)) := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    have h := hC.2 (mem_univ (L x)) (mem_univ (L y)) ha hb hab
    simpa only [Pi.neg_apply,neg_sub,map_add,map_smul,smul_eq_mul] using h
  have hSum := (contraction_quadratic_convex L hL hκ).add hComp
  convert hSum using 1
  funext x
  simp only [Pi.add_apply]
  ring

/-- A single global convex correction for the actual finite product
inf-convolution minus the finite C² comparison extension. The physical
base and time are still shared through the fixed maps Lᵢ. -/
theorem product_compactInfConvolution_jensen_convex {ι : Type*} [Fintype ι]
    (K : Set E) (v : E → ℝ) (hK : IsCompact K) (hNE : K.Nonempty)
    (hv : LowerSemicontinuousOn v K) (hv0 : ∀ s ∈ K, 0 ≤ v s)
    (L : ι → D →L[ℝ] E) (hL : ∀ i w, ‖L i w‖ ≤ ‖w‖)
    (α : ι → ℝ) (hα : ∀ i, 0 ≤ α i) {κ : ℝ} (hκ : 0 < κ)
    (g : D → ℝ) (C : ℝ) (hg : ConvexOn ℝ univ (fun x => g x+C*(‖x‖^2/2))) :
    ConvexOn ℝ univ (fun x =>
      -(∑ i, α i*compactInfConvolution K v κ (L i x)-g x)+
        ((∑ i, α i)/κ+C)*(‖x‖^2/2)) := by
  have hEach (i : ι) := ConvexOn.smul (hα i)
    (projected_compactInfConvolution_quadratic_convex K v hK hNE hv hv0 (L i) (hL i) hκ)
  have hSum : ConvexOn ℝ univ (fun x =>
      ∑ i, α i*(‖x‖^2/(2*κ)-compactInfConvolution K v κ (L i x))) := by
    refine ⟨convex_univ,?_⟩
    intro x _ y _ a b ha hb hab
    simp only [smul_eq_mul,Finset.mul_sum,←Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro i _
    exact (hEach i).2 (mem_univ x) (mem_univ y) ha hb hab
  have hAll := hSum.add hg
  convert hAll using 1
  funext x
  simp only [Pi.add_apply]
  simp only [mul_sub,Finset.sum_sub_distrib,←Finset.sum_mul]
  ring

end Yau.NodeProofs.E02Aux
