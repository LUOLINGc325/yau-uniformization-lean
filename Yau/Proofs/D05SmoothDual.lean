import Yau.Proofs.D05LocalDbar

/-! The explicit smooth dual of a nowhere-zero holomorphic vector and its
antisymmetric scalar correction coefficients. -/

open scoped Topology ContDiff
open Filter

noncomputable section
namespace Yau.Blueprint.D05Proof
open Yau

variable {ι : Type*} [Fintype ι]

def dualNormSum (e : ℂ → ι → ℂ) (z : ℂ) : ℝ := ∑ i, ‖e z i‖ ^ 2

def smoothDual (e : ℂ → ι → ℂ) (z : ℂ) (i : ι) : ℂ :=
  star (e z i) / (dualNormSum e z : ℂ)

def dualCorrection (e : ℂ → ι → ℂ) (z : ℂ) (j k : ι) : ℂ :=
  smoothDual e z j * wirtBar (fun w => smoothDual e w k) z 1 -
    smoothDual e z k * wirtBar (fun w => smoothDual e w j) z 1

theorem dualNormSum_pos {e : ℂ → ι → ℂ} {z : ℂ} (he : e z ≠ 0) :
    0 < dualNormSum e z := by
  classical
  obtain ⟨i, hi⟩ := Function.ne_iff.mp he
  apply Finset.sum_pos' (fun j _ => sq_nonneg ‖e z j‖)
  exact ⟨i, Finset.mem_univ _, sq_pos_of_pos (norm_pos_iff.mpr hi)⟩

theorem smoothDual_pairing {e : ℂ → ι → ℂ} {z : ℂ} (he : e z ≠ 0) :
    ∑ i, e z i * smoothDual e z i = 1 := by
  have hd : (dualNormSum e z : ℂ) ≠ 0 := by
    exact_mod_cast (dualNormSum_pos he).ne'
  have hsum : ∑ i, e z i * star (e z i) = (dualNormSum e z : ℂ) := by
    simp only [dualNormSum, Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.star_def, mul_comm, ← Complex.normSq_eq_conj_mul_self,
      Complex.normSq_eq_norm_sq]
  simp only [smoothDual, div_eq_mul_inv, ← mul_assoc, ← Finset.sum_mul, hsum]
  exact mul_inv_cancel₀ hd

theorem smoothDual_contDiffOn {U : Set ℂ} {e : ℂ → ι → ℂ}
    (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) (i : ι) :
    ContDiffOn ℝ ∞ (fun z => smoothDual e z i) U := by
  have hs : ContDiffOn ℝ ∞ (dualNormSum e) U :=
    ContDiffOn.sum (fun j _ => ((he j).restrict_scalars ℝ).norm_sq (𝕜 := ℂ))
  have hsI : ContDiffOn ℝ ∞ (fun z => (dualNormSum e z)⁻¹) U :=
    hs.inv (fun z hz => (dualNormSum_pos (hne z hz)).ne')
  have hsIC : ContDiffOn ℝ ∞ (fun z => ((dualNormSum e z)⁻¹ : ℝ)) U := hsI
  have hn : ContDiffOn ℝ ∞ (fun z => star (e z i)) U :=
    Complex.conjCLE.contDiff.comp_contDiffOn ((he i).restrict_scalars ℝ)
  have hprod : ContDiffOn ℝ ∞
      (fun z => star (e z i) * (((dualNormSum e z)⁻¹ : ℝ) : ℂ)) U :=
    hn.mul (Complex.ofRealCLM.contDiff.comp_contDiffOn hsIC)
  simpa only [smoothDual, div_eq_mul_inv, Complex.ofReal_inv] using hprod

theorem wirtBar_contDiffOn {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℂ}
    (hf : ContDiffOn ℝ ∞ f U) (v : ℂ) :
    ContDiffOn ℝ ∞ (fun z => wirtBar f z v) U := by
  have hD := hf.fderiv_of_isOpen hU (m := ∞) (by simp)
  exact contDiffOn_const.mul ((hD.clm_apply contDiffOn_const).add
    (contDiffOn_const.mul (hD.clm_apply contDiffOn_const)))

theorem dualCorrection_contDiffOn {U : Set ℂ} (hU : IsOpen U) {e : ℂ → ι → ℂ}
    (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) (j k : ι) :
    ContDiffOn ℝ ∞ (fun z => dualCorrection e z j k) U := by
  have hℓ := smoothDual_contDiffOn he hne
  exact ((hℓ j).mul (wirtBar_contDiffOn hU (hℓ k) 1)).sub
    ((hℓ k).mul (wirtBar_contDiffOn hU (hℓ j) 1))

theorem dualCorrection_antisymm (e : ℂ → ι → ℂ) (z : ℂ) (j k : ι) :
    dualCorrection e z j k = -dualCorrection e z k j := by
  unfold dualCorrection
  ring

theorem smoothDual_dbar_pairing {U : Set ℂ} (hU : IsOpen U) {e : ℂ → ι → ℂ}
    (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) {z : ℂ} (hz : z ∈ U) :
    ∑ i, e z i * wirtBar (fun w => smoothDual e w i) z 1 = 0 := by
  have hℓ := smoothDual_contDiffOn he hne
  have hde (i : ι) : DifferentiableAt ℂ (fun w => e w i) z :=
    ((he i z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hdℓ (i : ι) : DifferentiableAt ℝ (fun w => smoothDual e w i) z :=
    ((hℓ i z hz).contDiffAt (hU.mem_nhds hz)).differentiableAt (by simp)
  have hpair : (fun w => ∑ i, e w i * smoothDual e w i) =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact smoothDual_pairing (hne w hw)
  have hd : wirtBar (fun w => ∑ i, e w i * smoothDual e w i) z 1 = 0 := by
    simp only [wirtBar, hpair.fderiv_eq, fderiv_fun_const, Pi.zero_apply,
      zero_apply, mul_zero, add_zero]
  rw [V03Proof.wirtBar_sum Finset.univ (fun i w => e w i * smoothDual e w i) z 1
    (fun i _ => ((hde i).restrictScalars ℝ).mul (hdℓ i))] at hd
  simpa only [V03Proof.wirtBar_mul ((hde _).restrictScalars ℝ) (hdℓ _),
    V03Proof.wirtBar_holomorphic (hde _), zero_mul, zero_add] using hd

theorem dualCorrection_contraction {U : Set ℂ} (hU : IsOpen U) {e : ℂ → ι → ℂ}
    (he : ∀ i, ContDiffOn ℂ ∞ (fun z => e z i) U)
    (hne : ∀ z ∈ U, e z ≠ 0) {z : ℂ} (hz : z ∈ U) (k : ι) :
    ∑ j, e z j * dualCorrection e z j k =
      wirtBar (fun w => smoothDual e w k) z 1 := by
  simp only [dualCorrection, mul_sub, Finset.sum_sub_distrib]
  have h1 : (∑ j, e z j *
      (smoothDual e z j * wirtBar (fun w => smoothDual e w k) z 1)) =
      (∑ j, e z j * smoothDual e z j) * wirtBar (fun w => smoothDual e w k) z 1 := by
    simp only [Finset.sum_mul, mul_assoc]
  have h2 : (∑ j, e z j *
      (smoothDual e z k * wirtBar (fun w => smoothDual e w j) z 1)) =
      smoothDual e z k * ∑ j, e z j * wirtBar (fun w => smoothDual e w j) z 1 := by
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    ring
  rw [h1, h2, smoothDual_pairing (hne z hz), smoothDual_dbar_pairing hU he hne hz]
  ring

end Yau.Blueprint.D05Proof
