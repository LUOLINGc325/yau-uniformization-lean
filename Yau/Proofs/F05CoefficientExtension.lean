import Yau.Proofs.F05FlatRegions
import Yau.LeafProofs.L16HolderExtension

/-! The actual chart coefficients are extended by a literal convex cutoff,
retaining their exact values on the support of the physical patch. -/

open Set
open scoped Topology Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1800000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05CoefficientCutoff (n : ℕ) : Space n → ℝ := innerPatchBump 1 zero_lt_one 0

def F05PrincipalExtension (a : Point n → Mat n) (p : Point n) : Mat n :=
  F05CoefficientCutoff n p.1 • a p + (1-F05CoefficientCutoff n p.1) • (1 : Mat n)

def F05DriftExtension (b : Point n → RIdx n → ℝ) (p : Point n) (j : RIdx n) : ℝ :=
  F05CoefficientCutoff n p.1 * b p j

theorem F05_coefficient_cutoff_mem (A : AtlasData M) (i : Fin A.count) {T : ℝ}
    {p : Point n} (hp : p ∈ cylinder (closure (F05ModelOpen A i)) 0 T)
    (hNonzero : F05CoefficientCutoff n p.1 ≠ 0) : p ∈ F05Q A i T := by
  have hn := innerPatchBump_nonzero_norm_lt zero_lt_one hNonzero
  rw [sub_zero,mul_one] at hn
  have hFace := hp.1
  rw [F05ModelOpen_eq,F05FlatOpen_closure] at hFace
  exact ⟨⟨hn.le.trans (by norm_num),hFace⟩,hp.2⟩

theorem F05_coefficient_extension_budget (A : AtlasData M) (i : Fin A.count)
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ J : ℝ, 0 < J ∧ ∀ (T lam upper M₀ : ℝ) (a : Point n → Mat n)
      (b : Point n → RIdx n → ℝ), 0 ≤ M₀ →
      Elliptic (F05Q A i T) a lam upper → HolderBound α (F05Q A i T) a M₀ →
      (∀ j, HolderBound α (F05Q A i T) (fun p => b p j) M₀) →
      Elliptic (cylinder (closure (F05ModelOpen A i)) 0 T) (F05PrincipalExtension a)
        (min lam 1) (max upper 1) ∧
      HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T) (F05PrincipalExtension a) (J*(M₀+1)) ∧
      ∀ j, HolderBound α (cylinder (closure (F05ModelOpen A i)) 0 T)
        (fun p => F05DriftExtension b p j) (J*(M₀+1)) := by
  obtain ⟨P,hP,hCutoff⟩ := innerPatchBump_global_holderBound hα hα1 zero_lt_one (0 : Space n)
  let J := 1+2*P+2*(1+P)*‖(1 : Mat n)‖
  have hJ : 0 < J := by dsimp only [J]; positivity
  refine ⟨J,hJ,?_⟩
  intro T lam upper M₀ a b hM hEll ha hb
  let Q := cylinder (closure (F05ModelOpen A i)) 0 T
  have hCut : HolderBound α Q (fun p => F05CoefficientCutoff n p.1) P :=
    holderBound_mono hCutoff (subset_univ Q)
  have hZero : ∀ p ∈ Q, p ∉ F05Q A i T → F05CoefficientCutoff n p.1 = 0 := by
    intro p hp hpOut
    by_contra hNonzero
    exact hpOut (F05_coefficient_cutoff_mem A i hp hNonzero)
  have hProduct := holderBound_smul_cutoff_extension hCut
    (holderBound_mono ha (inter_subset_left : F05Q A i T ∩ Q ⊆ F05Q A i T)) hZero
  have hDrift (j : RIdx n) := holderBound_smul_cutoff_extension hCut
    (holderBound_mono (hb j) (inter_subset_left : F05Q A i T ∩ Q ⊆ F05Q A i T)) hZero
  have hOne := holderBound_one_sub hCut
  have hIdentity := holderBound_smul_refined hOne (holderBound_const α Q (1 : Mat n))
    hOne.1 (norm_nonneg _) (fun p hp => by simpa only [Real.norm_eq_abs] using hOne.2.1 p hp)
    (fun p _ => le_rfl)
  have hSum := holderBound_add hProduct hIdentity
  have hBudget : 2*P*M₀+((1+P)*‖(1 : Mat n)‖+(1+P)*‖(1 : Mat n)‖) ≤ J*(M₀+1) := by
    dsimp only [J]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2*(1+P)*‖(1 : Mat n)‖) hM]
  have hExtendedEll := elliptic_cutoff_extension (Q := Q) (χ := fun p => F05CoefficientCutoff n p.1)
    (φ := id) hEll
    (fun p _ => ⟨(innerPatchBump 1 zero_lt_one (0 : Space n)).nonneg,
      (innerPatchBump 1 zero_lt_one (0 : Space n)).le_one⟩)
    (fun p hp hNonzero => F05_coefficient_cutoff_mem A i hp hNonzero)
  refine ⟨hExtendedEll,holderBound_mono_const hSum hBudget,?_⟩
  intro j
  unfold F05DriftExtension
  have h := holderBound_mono_const (hDrift j)
    ((le_add_of_nonneg_right (by positivity : 0 ≤ (1+P)*‖(1 : Mat n)‖+(1+P)*‖(1 : Mat n)‖)).trans hBudget)
  simpa only [smul_eq_mul] using h

theorem F05_coefficient_extension_exact {a : Point n → Mat n} {b : Point n → RIdx n → ℝ}
    {p : Point n} (hp : ‖p.1‖ ≤ 1) :
    F05PrincipalExtension a p = a p ∧ ∀ j, F05DriftExtension b p j = b p j := by
  have hCut : F05CoefficientCutoff n p.1 = 1 := innerPatchBump_eq_one zero_lt_one (by simpa only [sub_zero] using hp)
  simp only [F05PrincipalExtension,F05DriftExtension,hCut,one_smul,sub_self,zero_smul,
    add_zero,one_mul,and_self,implies_true]

end Yau.Proofs.F05Aux
