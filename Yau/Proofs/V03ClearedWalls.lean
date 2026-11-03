import Yau.Proofs.V03ReciprocalLevi
import Yau.Proofs.V03LeviMatrix

/-! Polynomial representatives of reciprocal-wall Hessians. They retain
all derivatives of the actual cutoffs and extend across cutoff zeros. -/

open scoped Topology ContDiff Matrix
open Filter

noncomputable section
namespace Yau.Blueprint.V03Proof
open Yau

variable {E ι : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

theorem reciprocal_mixed_levi {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hne : f z ≠ 0) (v w : E) :
    wirt (fun y => wirtBar (fun x => (f x)⁻¹) y v) z w =
      2 * (f z)⁻¹ ^ 3 * wirt f z w * wirtBar f z v -
      (f z)⁻¹ ^ 2 * wirt (fun y => wirtBar f y v) z w := by
  have hd := hf.differentiableAt (by norm_num : (2 : ℕ∞ω) ≠ 0)
  have hi := hd.fun_inv hne
  have hB := wirtBar_differentiableAt hf v
  have heq : (fun y => wirtBar (fun x => (f x)⁻¹) y v) =ᶠ[𝓝 z]
      (fun y => -((f y)⁻¹ * (f y)⁻¹) * wirtBar f y v) := by
    filter_upwards [hf.eventually (by norm_num), hf.continuousAt.eventually_ne hne] with y hy hny
    rw [wirtBar_inv (hy.differentiableAt (by norm_num)) hny]
    ring
  have hw : wirt (fun y => wirtBar (fun x => (f x)⁻¹) y v) z w =
      wirt (fun y => -((f y)⁻¹ * (f y)⁻¹) * wirtBar f y v) z w := by
    unfold wirt
    rw [heq.fderiv_eq]
  rw [hw, wirt_mul (f := fun y => -((f y)⁻¹ * (f y)⁻¹)) (hi.mul hi).neg hB,
    wirt_neg, wirt_mul hi hi, wirt_inv hd hne]
  ring

def clearedReciprocalLevi (f : E → ℂ) (m : ℕ) (z v w : E) : ℂ :=
  2 * f z ^ (m - 3) * wirt f z w * wirtBar f z v -
    f z ^ (m - 2) * wirt (fun y => wirtBar f y v) z w

theorem clearedReciprocalLevi_eq {f : E → ℂ} {z : E}
    (hf : ContDiffAt ℝ 2 f z) (hne : f z ≠ 0) (v w : E) {m : ℕ} (hm : 3 ≤ m) :
    clearedReciprocalLevi f m z v w =
      f z ^ m * wirt (fun y => wirtBar (fun x => (f x)⁻¹) y v) z w := by
  rw [reciprocal_mixed_levi hf hne]
  unfold clearedReciprocalLevi
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hm
  have h32 : 3 + k - 2 = 1 + k := by omega
  rw [Nat.add_sub_cancel_left, h32]
  simp only [pow_add, pow_succ, pow_zero]
  field_simp [hne]

theorem wirt_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (v : E) : ContDiffOn ℝ ∞ (fun z => wirt f z v) U := by
  have hD := hf.fderiv_of_isOpen hU (m := ∞) (by simp)
  exact (contDiffOn_const (c := (1 / 2 : ℂ))).mul
    ((hD.clm_apply (contDiffOn_const (c := v))).sub
      ((contDiffOn_const (c := Complex.I)).mul
        (hD.clm_apply (contDiffOn_const (c := Complex.I • v)))))

theorem wirtBar_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (v : E) : ContDiffOn ℝ ∞ (fun z => wirtBar f z v) U := by
  have hD := hf.fderiv_of_isOpen hU (m := ∞) (by simp)
  exact (contDiffOn_const (c := (1 / 2 : ℂ))).mul
    ((hD.clm_apply (contDiffOn_const (c := v))).add
      ((contDiffOn_const (c := Complex.I)).mul
        (hD.clm_apply (contDiffOn_const (c := Complex.I • v)))))

theorem clearedReciprocalLevi_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (v w : E) :
    ContDiffOn ℝ ∞ (fun z => clearedReciprocalLevi f m z v w) U := by
  exact ((((contDiffOn_const (c := (2 : ℂ))).mul (hf.pow (m - 3))).mul
    (wirt_contDiffOn hU hf w)).mul (wirtBar_contDiffOn hU hf v)).sub
    ((hf.pow (m - 2)).mul (mixedWirt_contDiffOn hU hf v w))

def clearedReciprocalMatrix (f : E → ℝ) (m : ℕ) (dir : ι → E) (z : E) : Matrix ι ι ℂ :=
  fun a b => clearedReciprocalLevi (fun y => (f y : ℂ)) m z (dir a) (dir b)

theorem clearedReciprocalMatrix_entry_contDiffOn {U : Set E} (hU : IsOpen U) {f : E → ℝ}
    (hf : ContDiffOn ℝ ∞ f U) (m : ℕ) (dir : ι → E) (a b : ι) :
    ContDiffOn ℝ ∞ (fun z => clearedReciprocalMatrix f m dir z a b) U :=
  clearedReciprocalLevi_contDiffOn hU (Complex.ofRealCLM.contDiff.comp_contDiffOn hf) m
    (dir a) (dir b)

end Yau.Blueprint.V03Proof
