import Yau.LeafProofs.L16ChartCoefficientHolder
import Yau.LeafProofs.L16ChartEllipticity

open MeasureTheory Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 2400000
set_option synthInstance.maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- A real model principal field, changed to the identity beyond its
    artificial chart buffer; its true half-space face is retained. -/
def chartPrincipalCutoffExtension {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n)) (a : Point n → Mat n)
    (q : ℝ) (hq : 0 < q) (p : Point n) : Mat n :=
  innerPatchBump q hq 0 p.1 • chartTransformedPrincipal c a p+
    (1-innerPatchBump q hq 0 p.1) • (1 : Mat n)

def chartDriftCutoffExtension {n : ℕ}
    (c : OpenPartialHomeomorph (Space n) (Space n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (q : ℝ) (hq : 0 < q) (p : Point n) (i : Yau.RIdx n) : ℝ :=
  innerPatchBump q hq 0 p.1*chartTransformedDrift c a b p i

/-- Actual buffered chart coefficients extend to a compact perturbation of
    the identity on the entire closed half space. Holder and ellipticity
    losses are chosen geometrically before the original coefficient field. -/
theorem boundary_chart_compact_coefficient_extension {n : ℕ} {O : Set (Space n)}
    {α : ℝ} (hα : 0 < α) (hα1 : α < 1) (e : Space n)
    (c : OpenPartialHomeomorph (Space n) (Space n))
    (hc : ContDiffOn ℝ 3 c c.source) (hci : ContDiffOn ℝ 3 c.symm c.target)
    (hFaces : ∀ y ∈ c.source, y ∈ closure O ↔ 0 ≤ inner ℝ e (c y))
    {q : ℝ} (hq : 0 < q) (hTarget : Metric.closedBall (0 : Space n) (4*q) ⊆ c.target) :
    ∃ D J : ℝ, 1 ≤ D ∧ 0 < J ∧
      ∀ (T lam upper M : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
      0 ≤ M → Elliptic (cylinder (closure O) 0 T) a lam upper →
      HolderBound α (cylinder (closure O) 0 T) a M →
      (∀ i, HolderBound α (cylinder (closure O) 0 T) (fun p => b p i) M) →
      Elliptic (cylinder {y | 0 ≤ inner ℝ e y} 0 T) (chartPrincipalCutoffExtension c a q hq)
        (min (lam/D^2) 1) (max (upper*D^2) 1) ∧
      HolderBound α (cylinder {y | 0 ≤ inner ℝ e y} 0 T)
        (chartPrincipalCutoffExtension c a q hq) (J*(M+1)) ∧
      (∀ i, HolderBound α (cylinder {y | 0 ≤ inner ℝ e y} 0 T)
        (fun p => chartDriftCutoffExtension c a b q hq p i) (J*(M+1))) ∧
      (∀ p ∈ cylinder ({y | 0 ≤ inner ℝ e y}∩Metric.closedBall 0 q) 0 T,
        chartPrincipalCutoffExtension c a q hq p = chartTransformedPrincipal c a p ∧
        ∀ i, chartDriftCutoffExtension c a b q hq p i = chartTransformedDrift c a b p i) ∧
      ∀ p ∈ cylinder {y | 0 ≤ inner ℝ e y} 0 T,
        p.1 ∉ ({y | 0 ≤ inner ℝ e y}∩Metric.closedBall 0 (2*q)) →
        chartPrincipalCutoffExtension c a q hq p = 1 ∧
        ∀ i, chartDriftCutoffExtension c a b q hq p i = 0 := by
  let H : Set (Space n) := {y | 0 ≤ inner ℝ e y}
  let K : Set (Space n) := Metric.closedBall (0 : Space n) (3*q)
  let S : Set (Space n) := H∩K
  let φ : Space n → ℝ := innerPatchBump q hq 0
  have hKT : K ⊆ c.target :=
    (Metric.closedBall_subset_closedBall (by linarith : 3*q ≤ 4*q)).trans hTarget
  have hMap : MapsTo c.symm S (closure O) := by
    intro y hy
    apply (hFaces (c.symm y) (c.map_target (hKT hy.2))).mpr
    rw [c.right_inv (hKT hy.2)]
    exact hy.1
  obtain ⟨D,hD,hEllBudget⟩ := compact_chart_ellipticity_budget c hc hci
    (isCompact_closedBall 0 (3*q)) (convex_closedBall 0 (3*q)) hKT
  obtain ⟨C,hC,hHolderBudget⟩ := compact_chart_transformed_coefficients_holder hα hα1 c hc hci
    (isCompact_closedBall 0 (3*q)) (convex_closedBall 0 (3*q)) hKT
  obtain ⟨P,hP,hφ⟩ := innerPatchBump_global_holderBound hα hα1 hq (0 : Space n)
  let A : ℝ := 2*P*C
  let B : ℝ := 2*(1+P)*‖(1 : Mat n)‖
  let J : ℝ := 1+A+B
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hJ : 0 < J := by dsimp only [J]; positivity
  have hSupport : tsupport φ ⊆ K := by
    rw [(innerPatchBump q hq 0).tsupport_eq]
    exact Metric.closedBall_subset_closedBall (by linarith : 3*q/2 ≤ 3*q)
  have hSupport2 : tsupport φ ⊆ Metric.closedBall 0 (2*q) := by
    rw [(innerPatchBump q hq 0).tsupport_eq]
    exact Metric.closedBall_subset_closedBall (by linarith : 3*q/2 ≤ 2*q)
  refine ⟨D,J,hD,hJ,?_⟩
  intro T lam upper M a b hM hEll ha hb
  let Q := cylinder H 0 T
  have hModelEll := hEllBudget S (closure O) T lam upper a inter_subset_right hMap hEll
  obtain ⟨hModelA,hModelB⟩ := hHolderBudget S (closure O) T M a b inter_subset_right hMap ha hb
  have hCut : HolderBound α Q (fun p => φ p.1) P := holderBound_mono hφ (subset_univ Q)
  have hZero : ∀ p ∈ Q, p ∉ K×ˢ univ → φ p.1 = 0 := by
    intro p hp hOut
    apply image_eq_zero_of_notMem_tsupport
    intro hs
    exact hOut ⟨hSupport hs,mem_univ _⟩
  have hLocalSub : (K×ˢ univ)∩Q ⊆ cylinder S 0 T :=
    fun p hp => ⟨⟨hp.2.1,hp.1.1⟩,hp.2.2⟩
  have hProduct := holderBound_smul_cutoff_extension hCut (holderBound_mono hModelA hLocalSub) hZero
  have hDrift (i : Yau.RIdx n) := holderBound_smul_cutoff_extension hCut
    (holderBound_mono (hModelB i) hLocalSub) hZero
  have hOne := holderBound_one_sub hCut
  have hConst := holderBound_const α Q (1 : Mat n)
  have hIdentity := holderBound_smul_refined hOne hConst hOne.1 hConst.1
    (fun p hp => by simpa only [Real.norm_eq_abs] using hOne.2.1 p hp) hConst.2.1
  have hExtHolder := holderBound_add hProduct hIdentity
  have hBudget : 2*P*(C*M)+((1+P)*‖(1 : Mat n)‖+(1+P)*‖(1 : Mat n)‖) ≤ J*(M+1) := by
    calc
      _ = A*M+B := by dsimp only [A,B]; ring
      _ ≤ _ := by dsimp only [J]; nlinarith [mul_nonneg hB hM]
  have hExtEll := elliptic_cutoff_extension (Q := Q) (χ := fun p => φ p.1) (φ := id) hModelEll
    (fun p hp => ⟨(innerPatchBump q hq 0).nonneg,(innerPatchBump q hq 0).le_one⟩)
    (fun p hp hNonzero => ⟨⟨hp.1,hSupport (subset_tsupport φ (Function.mem_support.mpr hNonzero))⟩,hp.2⟩)
  refine ⟨hExtEll,holderBound_mono_const hExtHolder hBudget,?_,?_,?_⟩
  · intro i
    change HolderBound α Q (fun p => φ p.1*chartTransformedDrift c a b p i) (J*(M+1))
    have hh : HolderBound α Q (fun p => φ p.1*chartTransformedDrift c a b p i) (2*P*(C*M)) := by
      simpa only [smul_eq_mul] using hDrift i
    apply holderBound_mono_const hh
    exact (le_add_of_nonneg_right (by positivity : 0 ≤ (1+P)*‖(1 : Mat n)‖+(1+P)*‖(1 : Mat n)‖)).trans hBudget
  · intro p hp
    have hφ1 : φ p.1 = 1 := innerPatchBump_eq_one hq (by
      simpa only [Metric.mem_closedBall,dist_zero_right,sub_zero] using hp.1.2)
    simp only [chartPrincipalCutoffExtension,chartDriftCutoffExtension,hφ1,φ,one_smul,
      sub_self,zero_smul,add_zero,one_mul,and_self,implies_true]
  · intro p hp hOut
    have hφ0 : φ p.1 = 0 := by
      apply image_eq_zero_of_notMem_tsupport
      intro hs
      exact hOut ⟨hp.1,hSupport2 hs⟩
    simp only [chartPrincipalCutoffExtension,chartDriftCutoffExtension,hφ0,φ,zero_smul,
      sub_zero,one_smul,zero_add,zero_mul,and_self,implies_true]

end Yau.LeafProofs.L16Aux
