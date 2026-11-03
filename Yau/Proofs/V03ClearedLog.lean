import Yau.Proofs.V03ClearedWalls

/-! Exact cleared mixed derivatives of the actual real logarithm. The
polynomial representative has no reciprocal cutoff factors. -/

open scoped Topology ContDiff Matrix
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem log_real_mixed_levi {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hne : f z ≠ 0) (v w : E) :
    wirt (fun y => wirtBar (fun x => (Real.log (f x) : ℂ)) y v) z w =
      (f z : ℂ)⁻¹ * wirt (fun y => wirtBar (fun x => (f x : ℂ)) y v) z w -
        (f z : ℂ)⁻¹ ^ 2 * wirt (fun x => (f x : ℂ)) z w *
          wirtBar (fun x => (f x : ℂ)) z v := by
  have hF : ContDiffAt ℝ 2 (fun x => (f x : ℂ)) z :=
    hf.continuousLinearMap_comp Complex.ofRealCLM
  have hd := hF.differentiableAt (by norm_num)
  have hneC := Complex.ofReal_ne_zero.mpr hne
  have heq : (fun y => wirtBar (fun x => (Real.log (f x) : ℂ)) y v) =ᶠ[𝓝 z]
      (fun y => (f y : ℂ)⁻¹ * wirtBar (fun x => (f x : ℂ)) y v) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually_ne hne] with y hy hny
    exact wirtBar_log_real (hy.differentiableAt (by norm_num)) hny v
  have hw : wirt (fun y => wirtBar (fun x => (Real.log (f x) : ℂ)) y v) z w =
      wirt (fun y => (f y : ℂ)⁻¹ * wirtBar (fun x => (f x : ℂ)) y v) z w := by
    unfold wirt
    rw [heq.fderiv_eq]
  rw [hw, wirt_mul (f := fun y => (f y : ℂ)⁻¹) (hd.fun_inv hneC)
    (wirtBar_differentiableAt hF v), wirt_inv hd hneC]
  ring

def clearedLogLevi (f : E → ℝ) (m : ℕ) (z v w : E) : ℂ :=
  (f z : ℂ) ^ (m - 1) * wirt (fun y => wirtBar (fun x => (f x : ℂ)) y v) z w -
    (f z : ℂ) ^ (m - 2) * wirt (fun x => (f x : ℂ)) z w *
      wirtBar (fun x => (f x : ℂ)) z v

theorem clearedLogLevi_eq {f : E → ℝ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hne : f z ≠ 0) (v w : E) {m : ℕ} (hm : 2 ≤ m) :
    clearedLogLevi f m z v w = (f z : ℂ) ^ m *
      wirt (fun y => wirtBar (fun x => (Real.log (f x) : ℂ)) y v) z w := by
  rw [log_real_mixed_levi hf hne]
  unfold clearedLogLevi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h21 : 2 + k - 1 = 1 + k := by omega
  rw [Nat.add_sub_cancel_left, h21]
  simp only [pow_add, pow_succ, pow_zero]
  field_simp [Complex.ofReal_ne_zero.mpr hne]

theorem clearedLogLevi_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (v w : E) :
    ContDiffOn ℝ ∞ (fun z => clearedLogLevi f m z v w) U := by
  have hF : ContDiffOn ℝ ∞ (fun x => (f x : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hf
  exact ((hF.pow (m - 1)).mul (mixedWirt_contDiffOn hU hF v w)).sub
    (((hF.pow (m - 2)).mul (wirt_contDiffOn hU hF w)).mul (wirtBar_contDiffOn hU hF v))

end Yau.Blueprint.V03Proof
