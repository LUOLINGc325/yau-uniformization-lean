import Yau.LeafProofs.L05AutonomousSecondTensor
import Yau.LeafProofs.L05ABPAlgebra
import Yau.LeafProofs.L05AutonomousDirections

noncomputable section
open Filter Set MeasureTheory Matrix
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic Yau.LeafProofs.L05Aux

theorem auto_bilinear_upper_homogeneous {n : ℕ} (H : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    {P : ℝ} (hUpper : ∀ e : Space n, ‖e‖=1 → H e e ≤ P) (x : Space n) :
    H x x ≤ P*‖x‖^2 := by
  by_cases hx : x=0
  · simp only [hx,map_zero,norm_zero,zero_pow (by decide : (2 : ℕ)≠0),mul_zero,le_refl]
  have hn : ‖x‖≠0 := norm_ne_zero_iff.mpr hx
  have he : ‖‖x‖⁻¹ • x‖=1 := by
    rw [norm_smul,Real.norm_eq_abs,abs_inv,abs_of_nonneg (norm_nonneg x),inv_mul_cancel₀ hn]
  have h := mul_le_mul_of_nonneg_left (hUpper (‖x‖⁻¹ • x) he) (sq_nonneg ‖x‖)
  have heq : ‖x‖^2*H (‖x‖⁻¹ • x) (‖x‖⁻¹ • x)=H x x := by
    simp only [map_smul,_root_.smul_apply,smul_eq_mul]
    field_simp
  rw [heq] at h
  exact h.trans_eq (mul_comm _ _)

/-- A true upper quadratic bound makes the difference from the scalar identity positive semidefinite. -/
theorem auto_bilinear_upper_posSemidef {n : ℕ} (H : Space n →L[ℝ] Space n →L[ℝ] ℝ)
    (hSym : ∀ x y, H x y=H y x) {P : ℝ} (hUpper : ∀ e : Space n, ‖e‖=1 → H e e ≤ P) :
    (P • (1 : Mat n)-autoBilinearEntryMatrix H).PosSemidef := by
  have hM : (autoBilinearEntryMatrix H).IsHermitian := by
    apply Matrix.IsHermitian.ext
    intro i j
    simpa only [autoBilinearEntryMatrix,star_trivial] using hSym (Yau.realVec j) (Yau.realVec i)
  apply Matrix.PosSemidef.of_dotProduct_mulVec_nonneg
    ((Matrix.isHermitian_one.smul (IsSelfAdjoint.all P)).sub hM)
  intro v
  let x : Space n := ∑ i : Yau.RIdx n, v i • Yau.realVec i
  have hcoord (i : Yau.RIdx n) : inner ℝ (Yau.realVec i) x=v i := by
    simp [x,inner_sum,inner_smul_right,auto_realVec_inner]
  have hnorm : ‖x‖^2=∑ i, (v i)^2 := by
    have hh := autoRankOne_trace x
    rw [autoRankOne_coe] at hh
    change (∑ i, inner ℝ (Yau.realVec i) x*inner ℝ (Yau.realVec i) x)=‖x‖^2 at hh
    simpa only [hcoord,pow_two] using hh.symm
  have hform : H x x=∑ i, ∑ j, autoBilinearEntryMatrix H i j*v i*v j := by
    rw [auto_bilinear_entry_expansion]
    simp only [hcoord]
  have hBound := auto_bilinear_upper_homogeneous H hUpper x
  rw [hnorm,hform] at hBound
  have heq : star v ⬝ᵥ ((P • (1 : Mat n)-autoBilinearEntryMatrix H) *ᵥ v)=
      P*(∑ i, (v i)^2)-(∑ i, ∑ j, autoBilinearEntryMatrix H i j*v i*v j) := by
    simp only [star_trivial]
    rw [Matrix.sub_mulVec,Matrix.smul_mulVec,Matrix.one_mulVec]
    simp only [dotProduct,Pi.sub_apply,Pi.smul_apply,smul_eq_mul,mul_sub,Finset.sum_sub_distrib]
    rw [Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      ring
    · simp only [Matrix.mulVec,dotProduct,Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      ring
  rw [heq]
  exact sub_nonneg.mpr hBound

/-- The actual elliptic trace absorbs the negative Hessian directions with an explicit budget. -/
theorem auto_bilinear_frobenius_bound {n : ℕ} {ell L P B : ℝ} (hell : 0 < ell)
    (hP : 0 ≤ P) {A : Sym n} (hA : A∈slopeSet n ell L)
    (H : Space n →L[ℝ] Space n →L[ℝ] ℝ) (hSym : ∀ x y, H x y=H y x)
    (hUpper : ∀ e : Space n, ‖e‖=1 → H e e ≤ P)
    (hTrace : -B ≤ Matrix.trace ((A : Mat n)*autoBilinearEntryMatrix H)) :
    ‖autoBilinearEntryMatrix H‖ ≤
      P*‖(1 : Mat n)‖+(P*((2*n : ℝ)*L)+B)/ell := by
  let N : Mat n := P • (1 : Mat n)-autoBilinearEntryMatrix H
  have hN : N.PosSemidef := auto_bilinear_upper_posSemidef H hSym hUpper
  have hAN := posSemidef_trace_mul_nonneg hA.1 hN
  simp only [Matrix.sub_mul,Matrix.smul_mul,Matrix.one_mul,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul] at hAN
  have hAtrace : Matrix.trace (A : Mat n) ≤ (2*n : ℝ)*L := by
    calc
      _ ≤ ∑ _i : Yau.RIdx n, L := Finset.sum_le_sum fun i _ => by
        change (A : Mat n) i i ≤ L
        have hd := hA.2.diag_nonneg (i := i)
        simpa only [Matrix.sub_apply,Matrix.smul_apply,Matrix.one_apply_eq,smul_eq_mul,mul_one,sub_nonneg] using hd
      _ = _ := by
        simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Yau.RIdx,Fintype.card_prod,
          Fintype.card_fin,Nat.cast_mul,Nat.cast_ofNat]
        ring
  have hTraceN : Matrix.trace N ≤ (P*((2*n : ℝ)*L)+B)/ell := by
    have heq : Matrix.trace ((A : Mat n)*N)=
        P*Matrix.trace (A : Mat n)-Matrix.trace ((A : Mat n)*autoBilinearEntryMatrix H) := by
      simp only [N,Matrix.mul_sub,Matrix.mul_smul,Matrix.mul_one,Matrix.trace_sub,Matrix.trace_smul,smul_eq_mul]
    rw [heq] at hAN
    exact (le_div_iff₀ hell).mpr (by
      have hh := mul_le_mul_of_nonneg_left hAtrace hP
      nlinarith only [hAN,hh,hTrace])
  have hEq : autoBilinearEntryMatrix H=P • (1 : Mat n)-N := by dsimp only [N];abel
  calc
    _ = ‖P • (1 : Mat n)-N‖ := congrArg norm hEq
    _ ≤ ‖P • (1 : Mat n)‖+‖N‖ := norm_sub_le _ _
    _ ≤ P*‖(1 : Mat n)‖+Matrix.trace N := by
      rw [norm_smul,Real.norm_eq_abs,abs_of_nonneg hP]
      exact add_le_add (le_refl _) (posSemidef_norm_le_trace hN)
    _ ≤ _ := add_le_add (le_refl _) hTraceN

end Yau.LeafProofs.L05AutonomousAux
