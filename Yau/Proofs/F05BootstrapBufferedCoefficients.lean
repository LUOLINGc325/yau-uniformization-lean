import Yau.Proofs.F05BootstrapDefinitions
import Yau.LeafProofs.L16HolderExtension

/-! One fixed buffered coefficient extension is available for every
receiving compact cap strictly inside the supplied outer radius. Its numerical constant
is fixed before all nested radii, coefficients and difference quotients. -/

open Set
open scoped Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1600000
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ}

def F05BufferedPrincipal (χ : ContDiffBump (0 : Space n)) (a : Point n → Mat n) (z : Point n) : Mat n :=
  χ z.1 • a z+(1-χ z.1) • (1 : Mat n)

def F05BufferedDrift (χ : ContDiffBump (0 : Space n)) (b : Point n → RIdx n → ℝ) (z : Point n) (j : RIdx n) : ℝ :=
  χ z.1*b z j

theorem F05_buffered_coefficient_exact (χ : ContDiffBump (0 : Space n))
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {z : Point n} (hz : ‖z.1‖ ≤ χ.rIn) :
    F05BufferedPrincipal χ a z = a z ∧ ∀ j, F05BufferedDrift χ b z j = b z j := by
  have hCut := χ.one_of_mem_closedBall (by simpa only [Metric.mem_closedBall,dist_zero_right] using hz)
  simp only [F05BufferedPrincipal,F05BufferedDrift,hCut,one_smul,sub_self,zero_smul,add_zero,one_mul,
    and_self,implies_true]

theorem F05_buffered_coefficient_nonzero (χ : ContDiffBump (0 : Space n)) {x : Space n}
    (hx : χ x ≠ 0) : ‖x‖ < χ.rOut := by
  have hmem : x ∈ Function.support χ := hx
  rw [χ.support_eq] at hmem
  simpa only [Metric.mem_ball,dist_zero_right] using hmem

theorem F05_buffered_coefficient_exterior (χ : ContDiffBump (0 : Space n))
    {a : Point n → Mat n} {b : Point n → RIdx n → ℝ} {z : Point n} (hz : χ.rOut ≤ ‖z.1‖) :
    F05BufferedPrincipal χ a z = 1 ∧ ∀ j, F05BufferedDrift χ b z j = 0 := by
  have hCut : χ z.1 = 0 := by
    by_contra hn
    exact (not_lt_of_ge hz) (F05_buffered_coefficient_nonzero χ hn)
  simp only [F05BufferedPrincipal,F05BufferedDrift,hCut,zero_smul,sub_zero,one_smul,zero_add,zero_mul,
    and_self,implies_true]

theorem F05_buffered_coefficient_extension_budget (χ : ContDiffBump (0 : Space n))
    {Rbase : ℝ} (hχ : χ.rOut ≤ Rbase) {α : ℝ} (hα : 0 < α) (hα1 : α < 1) :
    ∃ J : ℝ, 0 < J ∧ ∀ (H : Set (Space n)) (I : Set ℝ) (lam upper M : ℝ)
      (a : Point n → Mat n) (b : Point n → RIdx n → ℝ), 0 ≤ M →
      Elliptic ((H ∩ Metric.closedBall 0 Rbase) ×ˢ I) a lam upper →
      HolderBound α ((H ∩ Metric.closedBall 0 Rbase) ×ˢ I) a M →
      (∀ j, HolderBound α ((H ∩ Metric.closedBall 0 Rbase) ×ˢ I) (fun z => b z j) M) →
      Elliptic (H ×ˢ I) (F05BufferedPrincipal χ a) (min lam 1) (max upper 1) ∧
      HolderBound α (H ×ˢ I) (F05BufferedPrincipal χ a) (J*(M+1)) ∧
      ∀ j, HolderBound α (H ×ˢ I) (fun z => F05BufferedDrift χ b z j) (J*(M+1)) := by
  obtain ⟨A,hA,hLip⟩ := smooth_compact_lipschitz χ.contDiff χ.hasCompactSupport
  let L := max 1 A
  have hL : 0 < L := lt_of_lt_of_le zero_lt_one (le_max_left _ _)
  let P := 2*L
  have hP : 0 < P := by dsimp only [P]; positivity
  have hCutoff : HolderBound α univ (fun z : Point n => χ z.1) P := by
    apply spatial_bounded_lipschitz_holderBound_univ hα hα1 hL.le
    · intro x
      rw [Real.norm_eq_abs,abs_of_nonneg χ.nonneg]
      exact χ.le_one.trans (le_max_left _ _)
    · intro x y
      exact (hLip x y).trans (mul_le_mul_of_nonneg_right (le_max_right _ _) (norm_nonneg _))
  let J := 1+2*P+2*(1+P)*‖(1 : Mat n)‖
  have hJ : 0 < J := by dsimp only [J]; positivity
  refine ⟨J,hJ,?_⟩
  intro H I lam upper M a b hM hEll ha hb
  let Q := H ×ˢ I
  let D := (H ∩ Metric.closedBall (0 : Space n) Rbase) ×ˢ I
  have hCut : HolderBound α Q (fun z => χ z.1) P := holderBound_mono hCutoff (subset_univ Q)
  have hNonzero (z : Point n) (hz : z ∈ Q) (hn : χ z.1 ≠ 0) : z ∈ D :=
    ⟨⟨hz.1,by simpa only [Metric.mem_closedBall,dist_zero_right] using
      ((F05_buffered_coefficient_nonzero χ hn).le.trans hχ)⟩,hz.2⟩
  have hZero : ∀ z ∈ Q, z ∉ D → χ z.1 = 0 := by
    intro z hz hOut
    by_contra hn
    exact hOut (hNonzero z hz hn)
  have hProduct := holderBound_smul_cutoff_extension hCut (holderBound_mono ha inter_subset_left) hZero
  have hDrift (j : RIdx n) := holderBound_smul_cutoff_extension hCut
    (holderBound_mono (hb j) inter_subset_left) hZero
  have hOne := holderBound_one_sub hCut
  have hIdentity := holderBound_smul_refined hOne (holderBound_const α Q (1 : Mat n))
    hOne.1 (norm_nonneg _) (fun z hz => by simpa only [Real.norm_eq_abs] using hOne.2.1 z hz)
    (fun z hz => le_rfl)
  have hSum := holderBound_add hProduct hIdentity
  have hBudget : 2*P*M+((1+P)*‖(1 : Mat n)‖+(1+P)*‖(1 : Mat n)‖) ≤ J*(M+1) := by
    dsimp only [J]
    nlinarith [mul_nonneg (by positivity : 0 ≤ 2*(1+P)*‖(1 : Mat n)‖) hM]
  refine ⟨elliptic_cutoff_extension (Q := Q) (χ := fun z => χ z.1) (φ := id) hEll
    (fun z hz => ⟨χ.nonneg,χ.le_one⟩) hNonzero,holderBound_mono_const hSum hBudget,?_⟩
  intro j
  have h := holderBound_mono_const (hDrift j)
    ((le_add_of_nonneg_right (by positivity : 0 ≤ (1+P)*‖(1 : Mat n)‖+(1+P)*‖(1 : Mat n)‖)).trans hBudget)
  simpa only [F05BufferedDrift,smul_eq_mul] using h

end Yau.Proofs.F05Aux
