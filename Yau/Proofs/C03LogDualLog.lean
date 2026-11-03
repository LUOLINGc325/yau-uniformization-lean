import Yau.Proofs.C03LogDualGraph
import Yau.Proofs.C03LogDualFirst
import Yau.Proofs.P04LeviLogChain

/-! The exact logarithmic completion and its genuine Cauchy-Schwarz remainder. -/
noncomputable section
open scoped Topology ContDiff Matrix ComplexOrder
open Set Filter
namespace Yau.Proofs.C03Aux.LogDual
open Yau Yau.Blueprint Yau.NodeProofs.E01Aux Yau.Blueprint.V03Proof Yau.LeafProofs L22Aux
set_option backward.isDefEq.respectTransparency false
set_option maxSynthPendingDepth 5
variable {n : ℕ}

theorem complexLeviQuadratic_log {f : ComplexVector n → ℝ} {z : ComplexVector n}
    (hf : ContDiffAt ℝ 2 f z) (hpos : 0 < f z) (a : ComplexVector n) :
    complexLeviQuadratic (fun w => Real.log (f w)) z a =
      complexLeviQuadratic f z a / f z -
        ‖wirt (fun w => (f w : ℂ)) z a‖ ^ 2 / (f z) ^ 2 := by
  have hn : ‖wirt (fun w => (f w : ℂ)) z a‖ ^ 2 =
      ((fderiv ℝ f z a) ^ 2 + (fderiv ℝ f z (Complex.I • a)) ^ 2) / 4 := by
    rw [Yau.Proofs.P04Aux.wirt_ofReal_formula (hf.differentiableAt (by norm_num)),
      ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, one_mul, mul_one,
      zero_add, add_zero, zero_sub, sub_zero]
    ring
  rw [hn]
  simp only [complexLeviQuadratic, Yau.Proofs.P04Aux.secondFDeriv_log hf hpos, div_eq_mul_inv]
  ring

theorem logDual_levi_completion {U : Set (ComplexVector n)} (hU : IsOpen U)
    (H : ComplexVector n → Herm n) (hHerm : ∀ z, (H z).IsHermitian)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef)
    (xi : ComplexVector n) (hxi : xi ≠ 0) (z : ComplexVector n) (hz : z ∈ U)
    (a : ComplexVector n) :
    complexLeviQuadratic (logDual H xi) z a =
      computedResidual H z xi a / dualSquared H xi z +
        (dualSquared H xi z * ellipsoidQuadratic ((H z)⁻¹)ᵀ (connectionVector H z xi a) -
          ‖matrixPairing ((H z)⁻¹)ᵀ xi (connectionVector H z xi a)‖ ^ 2) /
            (dualSquared H xi z) ^ 2 := by
  have hq : ContDiffAt ℝ 2 (dualSquared H xi) z :=
    ((dualSquared_contDiffOn H hH hPos xi).contDiffAt (hU.mem_nhds hz)).of_le (by simp)
  have hqp := dualSquared_pos (hPos z hz) hxi
  change complexLeviQuadratic (fun w => Real.log (dualSquared H xi w)) z a = _
  rw [complexLeviQuadratic_log hq hqp a,
    dualSquared_levi_completion hU H hHerm hH hPos z hz xi a,
    dualSquared_wirt hU H hHerm hH hPos z hz xi a]
  field_simp [hqp.ne'] <;> ring

theorem logDual_levi_ge_residual {U : Set (ComplexVector n)} (hU : IsOpen U)
    (H : ComplexVector n → Herm n) (hHerm : ∀ z, (H z).IsHermitian)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef)
    (xi : ComplexVector n) (hxi : xi ≠ 0) (z : ComplexVector n) (hz : z ∈ U)
    (a : ComplexVector n) :
    computedResidual H z xi a / dualSquared H xi z ≤
      complexLeviQuadratic (logDual H xi) z a := by
  have hc := matrixPairing_cauchy ((H z)⁻¹)ᵀ (hPos z hz).inv.transpose
    xi (connectionVector H z xi a)
  change ‖matrixPairing ((H z)⁻¹)ᵀ xi (connectionVector H z xi a)‖ ^ 2 ≤
    dualSquared H xi z * ellipsoidQuadratic ((H z)⁻¹)ᵀ (connectionVector H z xi a) at hc
  rw [logDual_levi_completion hU H hHerm hH hPos xi hxi z hz a]
  exact le_add_of_nonneg_right (div_nonneg (sub_nonneg.mpr hc) (sq_nonneg _))

theorem logDual_leviC_lower {U : Set (ComplexVector n)} (hU : IsOpen U)
    (H : ComplexVector n → Herm n) (hHerm : ∀ z, (H z).IsHermitian)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun z => H z i j) U)
    (hPos : ∀ z ∈ U, (H z).PosDef)
    (xi : ComplexVector n) (hxi : xi ≠ 0) (z : ComplexVector n) (hz : z ∈ U)
    (kappa : ℝ)
    (hR : ∀ a, kappa * dualSquared H xi z * ellipsoidQuadratic (H z) a ≤
      computedResidual H z xi a) :
    HermLE ((kappa : ℂ) • H z) (leviC (logDual H xi) z) := by
  have hpsi : ContDiffAt ℝ 2 (logDual H xi) z :=
    ((logDual_contDiffOn H hH hPos xi hxi).contDiffAt (hU.mem_nhds hz)).of_le (by simp)
  have hsm : (((kappa : ℂ) • H z) : Herm n).IsHermitian := by
    change ((kappa : ℂ) • H z)ᴴ = (kappa : ℂ) • H z
    rw [Matrix.conjTranspose_smul, (hHerm z).eq]
    simp
  apply (posSemidef_iff_ellipsoidQuadratic_nonneg _).mpr
  refine ⟨(leviC_isHermitian hpsi).sub hsm, ?_⟩
  intro a
  rw [ellipsoidQuadratic_sub, ellipsoidQuadratic_real_smul]
  have hq := dualSquared_pos (hPos z hz) hxi
  have hl : kappa * ellipsoidQuadratic (H z) a ≤
      computedResidual H z xi a / dualSquared H xi z := by
    apply (le_div_iff₀ hq).mpr
    simpa only [mul_assoc, mul_left_comm, mul_comm] using hR a
  have hr := logDual_levi_ge_residual hU H hHerm hH hPos xi hxi z hz a
  change 0 ≤ ellipsoidQuadratic (leviC (logDual H xi) z) a -
    kappa * ellipsoidQuadratic (H z) a
  rw [show ellipsoidQuadratic (leviC (logDual H xi) z) a =
    complexLeviQuadratic (logDual H xi) z a from leviC_quadratic_re hpsi a]
  exact sub_nonneg.mpr (hl.trans hr)

end Yau.Proofs.C03Aux.LogDual

