import Yau.LeafProofs.L05AutonomousHessianEnergy
import Yau.LeafProofs.L16CoefficientBounds

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

def autoBilinearEntryMatrix {n : ℕ} (B : Space n →L[ℝ] Space n →L[ℝ] ℝ) : Mat n :=
  fun i j => B (Yau.realVec i) (Yau.realVec j)

/-- Exact reconstruction in the actual real orthonormal coordinate frame. -/
theorem auto_bilinear_entry_expansion {n : ℕ} (B : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (v w : Space n) : B v w=∑ i, ∑ j, autoBilinearEntryMatrix B i j*
      inner ℝ (Yau.realVec i) v*inner ℝ (Yau.realVec j) w := by
  have hcoords (z : Space n) : (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) z • Yau.realVec i)=z := by
    simpa only [complexVector_realOrthonormalBasis_apply] using (complexVector_realOrthonormalBasis n).sum_repr' z
  calc
    _ = B (∑ i : Yau.RIdx n, inner ℝ (Yau.realVec i) v • Yau.realVec i)
        (∑ j : Yau.RIdx n, inner ℝ (Yau.realVec j) w • Yau.realVec j) := by rw [hcoords,hcoords]
    _ = _ := by
      simp only [map_sum,map_smul,_root_.sum_apply,_root_.smul_apply,smul_eq_mul,Finset.mul_sum,autoBilinearEntryMatrix]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

/-- The dimensional budget is explicit and precedes every bilinear form. -/
theorem auto_bilinear_entry_budget (n : ℕ) : ∃ C : ℝ, 0< C ∧
    ∀ B : Space n →L[ℝ] Space n →L[ℝ] ℝ,
    ∀ v : Space n, ‖v‖≤ 1 → |B v v|≤ C*‖autoBilinearEntryMatrix B‖ := by
  let C : ℝ := (2*n : ℝ)^2+1
  have hC : 0< C := by dsimp only [C];positivity
  refine ⟨C,hC,?_⟩
  intro B v hv
  have hcoord (i : Yau.RIdx n) : |inner ℝ (Yau.realVec i) v|≤ 1 := by
    have he : ‖Yau.realVec i‖=1 := by
      simpa only [complexVector_realOrthonormalBasis_apply] using (complexVector_realOrthonormalBasis n).orthonormal.norm_eq_one i
    have hh := norm_inner_le_norm (𝕜 := ℝ) (Yau.realVec i) v
    rw [Real.norm_eq_abs,he,one_mul] at hh
    exact hh.trans hv
  have hentry (i j : Yau.RIdx n) : |autoBilinearEntryMatrix B i j|≤ ‖autoBilinearEntryMatrix B‖ :=
    L16Aux.frobenius_entry_abs_le _ _ _
  have hmain : |B v v|≤ (2*n : ℝ)^2*‖autoBilinearEntryMatrix B‖ := by
    rw [auto_bilinear_entry_expansion]
    calc
      _ ≤ ∑ i : Yau.RIdx n, |∑ j : Yau.RIdx n, autoBilinearEntryMatrix B i j*inner ℝ (Yau.realVec i) v*inner ℝ (Yau.realVec j) v| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Yau.RIdx n, ∑ j : Yau.RIdx n, ‖autoBilinearEntryMatrix B‖ := by
        apply Finset.sum_le_sum
        intro i _
        exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ => by
          rw [abs_mul,abs_mul]
          calc
            _ ≤ ‖autoBilinearEntryMatrix B‖*1*1 := by gcongr;exact hentry i j;exact hcoord i;exact hcoord j
            _ = _ := by ring)
      _ = _ := by simp [Yau.RIdx];ring
  exact hmain.trans (by dsimp only [C];nlinarith only [norm_nonneg (autoBilinearEntryMatrix B)])

/-- This controls the actual directional Hessian by the actual Frobenius matrix used by K. -/
theorem auto_second_direction_budget (n : ℕ) : ∃ C : ℝ, 0< C ∧
    ∀ f : Space n → ℝ, ∀ x e : Space n, ‖e‖≤ 1 →
      |fderiv ℝ (fderiv ℝ f) x e e|≤ C*‖secondFDerivMatrix f x‖ := by
  obtain ⟨C,hC,hbound⟩ := auto_bilinear_entry_budget n
  exact ⟨C,hC,fun f x e he => hbound (fderiv ℝ (fderiv ℝ f) x) e he⟩

end Yau.LeafProofs.L05AutonomousAux
