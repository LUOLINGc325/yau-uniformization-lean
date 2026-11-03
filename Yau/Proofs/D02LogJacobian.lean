import Yau.Proofs.D02JacobianTransition
import Yau.Proofs.V03LogSumPositive

/-! The actual Gram determinant is the sum of squared holomorphic minors.
Its logarithm has a nonnegative Levi form in every valid fixed chart. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux
open Yau Yau.Blueprint Yau.Blueprint.V03Proof
set_option backward.isDefEq.respectTransparency false

variable {n N : ℕ} {M : ComplexManifold n}

def immersionMinor (F : M.Carrier → ComplexVector N) (x : M.Carrier)
    (p : Fin n → Fin N) (z : ComplexVector n) : ℂ :=
  (immersionDerivativeMatrix F x z |>.submatrix p id).det

theorem immersionMinor_contDiffOn {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (x : M.Carrier) (p : Fin n → Fin N) :
    ContDiffOn ℂ ∞ (immersionMinor F x p) (chartTarget x) := by
  change ContDiffOn ℂ ∞
    (fun z => (immersionDerivativeMatrix F x z |>.submatrix p id).det) (chartTarget x)
  simp_rw [Matrix.det_apply', Matrix.submatrix_apply, id_eq]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul
    (contDiffOn_prod fun i _ => complex_holomorphic_contDiffOn
      (isOpen_extChartAt_target (I := ComplexModel n) x)
      (immersionDerivativeMatrix_differentiableOn hF x (p (σ i)) i))

theorem immersionGram_det_re_eq (F : M.Carrier → ComplexVector N) (x : M.Carrier)
    (z : ComplexVector n) :
    (immersionGram F x z).det.re = (Fintype.card (Equiv.Perm (Fin n)) : ℝ)⁻¹ *
      holomorphicSqSum (immersionMinor F x) z :=
  gram_det_re_eq_sum_tuple_minors (immersionDerivativeMatrix F x z)

theorem immersionMinorSquareSum_pos {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    0 < holomorphicSqSum (immersionMinor F x) z := by
  have hcard : 0 < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  have hpos := (Complex.pos_iff.mp (immersionGram_posDef hF hImm x hz).det_pos).1
  rw [immersionGram_det_re_eq] at hpos
  exact (mul_pos_iff_of_pos_left (inv_pos.mpr hcard)).mp hpos

theorem log_immersionGram_det_re_eq {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    Real.log (immersionGram F x z).det.re =
      Real.log (holomorphicSqSum (immersionMinor F x) z) -
        Real.log (Fintype.card (Equiv.Perm (Fin n)) : ℝ) := by
  have hcard : 0 < (Fintype.card (Equiv.Perm (Fin n)) : ℝ) :=
    Nat.cast_pos.mpr Fintype.card_pos
  rw [immersionGram_det_re_eq, Real.log_mul (inv_ne_zero hcard.ne')
    (immersionMinorSquareSum_pos hF hImm x hz).ne', Real.log_inv]
  ring

theorem log_immersionGram_contDiffOn {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) (x : M.Carrier) :
    ContDiffOn ℝ ∞ (fun z => Real.log (immersionGram F x z).det.re) (chartTarget x) := by
  have hG := Complex.reCLM.contDiff.comp_contDiffOn
    (entrywise_matrix_det_contDiffOn (immersionGram_entry_contDiffOn hF x))
  exact hG.log (fun z hz => (Complex.pos_iff.mp (immersionGram_posDef hF hImm x hz).det_pos).1.ne')

/-- The two genuine calculators for the real diagonal Levi value agree. -/
theorem mixedWirt_real_eq_LeviQuadratic {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (v : ComplexVector n) :
    (wirt (fun y => wirtBar (fun y' => (f y' : ℂ)) y v) z v).re =
      Yau.LeafProofs.L22Aux.complexLeviQuadratic f z v := by
  have h := Yau.LeafProofs.L18Aux.leviMatrix_diag_re hf (fun _ : Unit => v) ()
  change (wirt (fun y => wirtBar (fun y' => (f y' : ℂ)) y v) z v).re = _ at h
  rw [h]
  unfold Yau.LeafProofs.L22Aux.complexLeviQuadratic
  ring

/-- This is the nonnegative term in the source's actual ψ calculation. -/
theorem log_immersionGram_levi_posSemidef {F : M.Carrier → ComplexVector N}
    (hF : IsHolomorphicVecMap F) (hImm : IsImmersionMap F) (x : M.Carrier)
    {z : ComplexVector n} (hz : z ∈ chartTarget x) :
    (leviC (fun w => Real.log (immersionGram F x w).det.re) z).PosSemidef := by
  have hG : ContDiffAt ℝ 2 (fun w => Real.log (immersionGram F x w).det.re) z :=
    ((log_immersionGram_contDiffOn hF hImm x).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp)
  apply (Yau.LeafProofs.L22Aux.leviC_posSemidef_iff hG).mpr
  intro v
  rw [← mixedWirt_real_eq_LeviQuadratic hG v]
  have heq : (fun w => (Real.log (immersionGram F x w).det.re : ℂ)) =ᶠ[𝓝 z]
      (fun w => (Real.log (holomorphicSqSum (immersionMinor F x) w) : ℂ) +
        (-Real.log (Fintype.card (Equiv.Perm (Fin n)) : ℝ) : ℂ)) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz] with w hw
    rw [log_immersionGram_det_re_eq hF hImm x hw, Complex.ofReal_sub]
    simp only [sub_eq_add_neg]
  rw [mixedWirt_congr heq, mixedWirt_add_const]
  exact log_holomorphicSqSum_levi_nonneg
    (fun p => ((immersionMinor_contDiffOn hF x p).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)).of_le (by simp))
    (immersionMinorSquareSum_pos hF hImm x hz) v

end Yau.NodeProofs.D02Aux
