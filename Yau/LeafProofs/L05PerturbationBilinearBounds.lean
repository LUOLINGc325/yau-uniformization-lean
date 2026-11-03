import Yau.LeafProofs.L05PerturbationPolynomials
import Yau.LeafProofs.L05ComplexRepresentation

open Set Metric Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem perturb_real_coordinates_norm {n : ℕ} (x : Space n) :
    ‖WithLp.toLp 2 (fun i : RIdx n => inner ℝ (realVec i) x)‖=‖x‖ := by
  have he : WithLp.toLp 2 (fun i : RIdx n => inner ℝ (realVec i) x)=
      (complexVector_realOrthonormalBasis n).repr x := by
    ext i
    simp [OrthonormalBasis.repr_apply_apply,complexVector_realOrthonormalBasis_apply]
  rw [he]
  exact (complexVector_realOrthonormalBasis n).repr.norm_map x

theorem perturbBilinear_apply_norm_le {n : ℕ} (A : Sym n) (v w : Space n) :
    ‖perturbBilinear A v w‖≤‖A‖*‖v‖*‖w‖ := by
  classical
  let row : Matrix Unit (RIdx n) ℝ := Matrix.replicateRow Unit (fun i => inner ℝ (realVec i) v)
  let col : Matrix (RIdx n) Unit ℝ := Matrix.replicateCol Unit (fun i => inner ℝ (realVec i) w)
  have he : (row*(A : Mat n)*col) () ()=perturbBilinear A v w := by
    simp only [Matrix.mul_apply,row,col,Matrix.replicateRow_apply,Matrix.replicateCol_apply,
      Finset.sum_mul,perturbBilinear_apply]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    apply Finset.sum_congr rfl
    intro j hj
    ring
  have hn : ‖row*(A : Mat n)*col‖=‖perturbBilinear A v w‖ := by
    calc
      _ = Real.sqrt (‖(row*(A : Mat n)*col) () ()‖^2) := by
        rw [Matrix.frobenius_norm_def]
        simp only [Fintype.sum_unique,Real.rpow_two,Real.sqrt_eq_rpow]
      _ = ‖(row*(A : Mat n)*col) () ()‖ := Real.sqrt_sq (norm_nonneg _)
      _ = _ := by rw [he]
  have hr : ‖row‖=‖v‖ := by
    rw [show row=Matrix.replicateRow Unit (fun i => inner ℝ (realVec i) v) from rfl,
      Matrix.frobenius_norm_replicateRow]
    exact perturb_real_coordinates_norm v
  have hc : ‖col‖=‖w‖ := by
    rw [show col=Matrix.replicateCol Unit (fun i => inner ℝ (realVec i) w) from rfl,
      Matrix.frobenius_norm_replicateCol]
    exact perturb_real_coordinates_norm w
  calc
    _ = ‖row*(A : Mat n)*col‖ := hn.symm
    _ ≤ ‖row*(A : Mat n)‖*‖col‖ := Matrix.frobenius_norm_mul _ _
    _ ≤ (‖row‖*‖(A : Mat n)‖)*‖col‖ :=
      mul_le_mul_of_nonneg_right (Matrix.frobenius_norm_mul row (A : Mat n)) (norm_nonneg _)
    _ = _ := by rw [hr,hc]; change (‖v‖*‖A‖)*‖w‖=‖A‖*‖v‖*‖w‖; ring

theorem perturbBilinear_norm_le {n : ℕ} (A : Sym n) : ‖perturbBilinear A‖≤‖A‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg A)
  intro v
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg (norm_nonneg A) (norm_nonneg v))
  intro w
  exact perturbBilinear_apply_norm_le A v w

theorem perturb_matrix_norm_le_card {n : ℕ} (A : Sym n) :
    ‖A‖≤(Fintype.card (RIdx n) : ℝ)*‖perturbBilinear A‖ := by
  classical
  have he : ∀ i j : RIdx n, |(A : Mat n) i j|≤‖perturbBilinear A‖ := by
    intro i j
    rw [←perturbBilinear_realVec A i j,←Real.norm_eq_abs]
    have hi : ‖realVec i‖=1 := by simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).norm_eq_one i
    have hj : ‖realVec j‖=1 := by simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).norm_eq_one j
    calc
      _ ≤ ‖perturbBilinear A (realVec i)‖*‖realVec j‖ :=
        (perturbBilinear A (realVec i)).le_opNorm _
      _ ≤ (‖perturbBilinear A‖*‖realVec i‖)*‖realVec j‖ :=
        mul_le_mul_of_nonneg_right ((perturbBilinear A).le_opNorm _) (norm_nonneg _)
      _ = _ := by rw [hi,hj,mul_one,mul_one]
  have hsq : ‖A‖^2=∑ i, ∑ j, |(A : Mat n) i j|^2 := by
    change ‖(A : Mat n)‖^2=_
    rw [Matrix.frobenius_norm_def]
    simp only [Real.rpow_two,Real.norm_eq_abs]
    rw [←Real.sqrt_eq_rpow,Real.sq_sqrt (by positivity)]
  have hb : (∑ i, ∑ j, |(A : Mat n) i j|^2)≤
      (Fintype.card (RIdx n) : ℝ)^2*‖perturbBilinear A‖^2 := by
    calc
      _ ≤ ∑ _i : RIdx n, ∑ _j : RIdx n, ‖perturbBilinear A‖^2 := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        exact (sq_le_sq₀ (abs_nonneg ((A : Mat n) i j)) (norm_nonneg (perturbBilinear A))).mpr (he i j)
      _ = _ := by simp; ring
  have hp : 0≤(Fintype.card (RIdx n) : ℝ)*‖perturbBilinear A‖ := by positivity
  apply (sq_le_sq₀ (norm_nonneg A) hp).mp
  rw [hsq,mul_pow]
  exact hb


theorem perturb_spatialDD_eq_bilinear {n : ℕ} {Q : Set (Point n)}
    {u : Point n → ℝ} (hu : C2 Q u) {p : Point n} (hp : p∈Q) :
    spatialDD u p=perturbBilinear (hessian u p) := by
  have hm : (hessian u p : Mat n)=
      (fun i j => spatialDD u p (realVec i) (realVec j)) :=
    hessian_space_eq_secondFDeriv (hu.2.2.2.2.1 p hp)
  ext v w
  have hv : (∑ i : RIdx n, inner ℝ (realVec i) v • realVec i)=v := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).sum_repr' v
  have hw : (∑ i : RIdx n, inner ℝ (realVec i) w • realVec i)=w := by
    simpa only [complexVector_realOrthonormalBasis_apply] using
      (complexVector_realOrthonormalBasis n).sum_repr' w
  rw [←hv,←hw]
  simp [map_sum,map_smul,perturbBilinear_realVec,hm]

theorem perturb_hessian_norm_le {n : ℕ} {Q : Set (Point n)}
    {u : Point n → ℝ} (hu : C2 Q u) {p : Point n} (hp : p∈Q) :
    ‖hessian u p‖≤(Fintype.card (RIdx n) : ℝ)*‖spatialDD u p‖ := by
  have hh := perturb_matrix_norm_le_card (hessian u p)
  rwa [←perturb_spatialDD_eq_bilinear hu hp] at hh

theorem perturb_spatialDD_norm_le {n : ℕ} {Q : Set (Point n)}
    {u : Point n → ℝ} (hu : C2 Q u) {p : Point n} (hp : p∈Q) :
    ‖spatialDD u p‖≤‖hessian u p‖ := by
  rw [perturb_spatialDD_eq_bilinear hu hp]
  exact perturbBilinear_norm_le _

theorem perturbQuad_abs_le {n : ℕ} (A : Sym n) (x : Space n) :
    |perturbQuad A x|≤‖A‖*‖x‖^2 := by
  simpa only [perturbQuad_eq_bilinear,Real.norm_eq_abs,pow_two,mul_assoc] using
    perturbBilinear_apply_norm_le A x x

end Yau.LeafProofs.L05Aux
