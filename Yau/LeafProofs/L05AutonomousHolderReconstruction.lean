import Yau.LeafProofs.L05AutonomousContinuousRepresentative
import Yau.LeafProofs.L05AutonomousLocalFrame

noncomputable section
open Set Filter MeasureTheory
open scoped Topology Matrix Matrix.Norms.Frobenius
set_option maxHeartbeats 2400000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05AutonomousAux
open Yau.Parabolic

/-- The fixed finite directional reconstruction transfers actual directional
pair bounds to the native Frobenius norm. No derivative of H is assumed. -/
theorem auto_direction_holder_reconstruction {n N : ℕ} (e : Fin N → Space n)
    (hRecon : ∀ H : Sym n, ‖H‖ ≤ (2*n : ℝ)*2*∑ j, |autoBilinearMap n H (e j) (e j)|)
    {S : Set (Point n)} {eta K : ℝ} {H : Point n → Sym n}
    (hDir : ∀ j, ∀ p∈S, ∀ q∈S,
      |autoBilinearMap n (H p) (e j) (e j)-autoBilinearMap n (H q) (e j) (e j)| ≤
        K*holderWeight eta p q) :
    ∀ p∈S, ∀ q∈S, ‖H p-H q‖ ≤ (2*n : ℝ)*2*(N : ℝ)*K*holderWeight eta p q := by
  intro p hp q hq
  have hFields (j : Fin N) : |autoBilinearMap n (H p-H q) (e j) (e j)| ≤ K*holderWeight eta p q := by
    simpa only [map_sub,_root_.sub_apply] using hDir j p hp q hq
  have hSum := Finset.sum_le_sum (fun j (_ : j∈Finset.univ) => hFields j)
  have hMain := (hRecon (H p-H q)).trans
    (mul_le_mul_of_nonneg_left hSum (by positivity : (0 : ℝ) ≤ (2*n : ℝ)*2))
  convert hMain using 1 <;>
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] <;> ring

/-- A given continuous representative retains a full-measure good-set pair
bound on the entire genuine closed cylinder, including top and lateral faces. -/
theorem auto_continuous_holder_on_full_cylinder {n : ℕ} {E : Type*}
    [NormedAddCommGroup E] [CompleteSpace E] (c : Space n) {R T : ℝ} (hR : 0 < R)
    {S : Set (Point n)} (hS : S ⊆ autoOpen c R T)
    (hFull : ∀ᵐ p ∂volume.restrict (autoOpen c R T), p∈S)
    {eta C B : ℝ} (heta : 0 < eta) (hC : 0 ≤ C) (hB : 0 ≤ B)
    (f : Point n → E) (hf : ContinuousOn f (autoClosed c R T))
    (hBound : ∀ p∈S, ‖f p‖ ≤ B)
    (hHolder : ∀ p∈S, ∀ q∈S, ‖f p-f q‖ ≤ C*holderWeight eta p q) :
    (∀ p∈autoClosed c R T, ‖f p‖ ≤ B) ∧
      (∀ p∈autoClosed c R T, ∀ q∈autoClosed c R T,
        ‖f p-f q‖ ≤ C*holderWeight eta p q) := by
  obtain ⟨g,hg,hEq,hgb,hgh⟩ := auto_full_measure_cylinder_holder_representative c hR hS hFull
    heta hC hB f hBound hHolder
  have hSK : S ⊆ autoClosed c R T := fun p hp =>
    ⟨Metric.ball_subset_closedBall (hS hp).1,⟨(hS hp).2.1.le,(hS hp).2.2.le⟩⟩
  have hAll : EqOn g f (autoClosed c R T) :=
    hEq.of_subset_closure hg hf hSK (auto_full_measure_cylinder_closure c hR hS hFull).ge
  constructor
  · intro p hp
    rw [← hAll hp]
    exact hgb p hp
  · intro p hp q hq
    rw [← hAll hp,← hAll hq]
    exact hgh p hp q hq

end Yau.LeafProofs.L05AutonomousAux
