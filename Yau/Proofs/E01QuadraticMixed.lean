import Yau.Proofs.E01QuadraticSecond
import Yau.Proofs.E01MixedFiniteSum
import Yau.Proofs.E01MatrixWirtinger

/-! The exact four-term mixed derivative of a quadratic fiber norm. -/

noncomputable section
open scoped Matrix Topology

namespace Yau.NodeProofs.E01Aux
open Yau Yau.Blueprint

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {n : ℕ}

theorem mixedWirt_quadratic_fiber (A : E → Herm n) (L : E →L[ℂ] ComplexVector n)
    (z v : E) (hA : ∀ i j, ContDiffAt ℝ 2 (fun w => A w i j) z) :
    wirt (fun w => wirtBar (fun y =>
      star (WithLp.ofLp (L y)) ⬝ᵥ (A y *ᵥ WithLp.ofLp (L y))) w v) z v =
      star (WithLp.ofLp (L v)) ⬝ᵥ (A z *ᵥ WithLp.ofLp (L v)) +
      star (WithLp.ofLp (L v)) ⬝ᵥ (complexMatrixWirt A z v *ᵥ WithLp.ofLp (L z)) +
      star (WithLp.ofLp (L z)) ⬝ᵥ (complexMatrixWirtBar A z v *ᵥ WithLp.ofLp (L v)) +
      star (WithLp.ofLp (L z)) ⬝ᵥ
        (complexMatrixWirt (fun w => complexMatrixWirtBar A w v) z v *ᵥ WithLp.ofLp (L z)) := by
  let ℓ : Fin n → E →L[ℂ] ℂ := fun i => (EuclideanSpace.proj i).comp L
  let F : Fin n → Fin n → E → ℂ := fun i j w => star (ℓ i w) * A w i j * ℓ j w
  have hF (i j : Fin n) : ContDiffAt ℝ 2 (F i j) z :=
    ((Complex.conjCLE.contDiff.contDiffAt.comp z ((ℓ i).contDiff.contDiffAt.restrict_scalars ℝ)).mul
      (hA i j)).mul ((ℓ j).contDiff.contDiffAt.restrict_scalars ℝ)
  have hFSum (i : Fin n) : ContDiffAt ℝ 2 (fun w => ∑ j, F i j w) z :=
    ContDiffAt.sum (fun j _ => hF i j)
  have hpair : (fun y => star (WithLp.ofLp (L y)) ⬝ᵥ (A y *ᵥ WithLp.ofLp (L y))) =
      (fun y => ∑ i, ∑ j, F i j y) := by
    funext y
    simp only [dotProduct, Matrix.mulVec, Pi.star_apply, Finset.mul_sum, F, ℓ,
      ContinuousLinearMap.comp_apply, PiLp.proj_apply]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [hpair, mixedWirt_fintype_sum (fun i y => ∑ j, F i j y) z v hFSum]
  have hinner (i : Fin n) := mixedWirt_fintype_sum (F i) z v (hF i)
  simp_rw [hinner]
  have hterm (i j : Fin n) := mixedWirt_quadratic_summand (ℓ i) (ℓ j) (hA i j) v
  change (∑ i, ∑ j, wirt (fun w => wirtBar (F i j) w v) z v) = _
  simp_rw [show ∀ i j, wirt (fun w => wirtBar (F i j) w v) z v =
    star (ℓ i v) * A z i j * ℓ j v + star (ℓ i v) * wirt (fun w => A w i j) z v * ℓ j z +
    star (ℓ i z) * wirtBar (fun w => A w i j) z v * ℓ j v +
    star (ℓ i z) * wirt (fun w => wirtBar (fun y => A y i j) w v) z v * ℓ j z from hterm]
  simp only [dotProduct, Matrix.mulVec, Pi.star_apply, complexMatrixWirt, complexMatrixWirtBar,
    ℓ, ContinuousLinearMap.comp_apply, PiLp.proj_apply, Finset.mul_sum,
    Finset.sum_add_distrib, mul_assoc]

end Yau.NodeProofs.E01Aux
