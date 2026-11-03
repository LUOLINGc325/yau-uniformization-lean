import Yau.LeafProofs.L16NearPairHolder

open MeasureTheory Filter Set
open scoped Topology ContDiff
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic

/-- A compact spatial cover with genuine local Holder budgets gives one
    global budget chosen before the function. Close pairs lie in one buffered
    ball; the existing near-pair theorem supplies all far pairs. -/
theorem compact_spatial_local_holder_glue {n : ℕ} {E : Type*} [NormedAddCommGroup E]
    {K : Set (Space n)} (hK : IsCompact K) {α T : ℝ} (hα : 0 ≤ α)
    (r A : K → ℝ) (hr : ∀ i, 0 < r i) (hA : ∀ i, 0 ≤ A i) :
    ∃ C : ℝ, 0 < C ∧ ∀ (f : Point n → E) P, 0 ≤ P →
      (∀ p ∈ cylinder K 0 T, ‖f p‖ ≤ P) →
      (∀ i : K, HolderBound α (cylinder (K∩Metric.closedBall (i : Space n) (r i)) 0 T) f (A i*P)) →
      HolderBound α (cylinder K 0 T) f (C*P) := by
  classical
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover (fun i : K => Metric.ball (i : Space n) (r i/2))
    (fun _ => Metric.isOpen_ball) (by
      intro x hx
      exact mem_iUnion.mpr ⟨⟨x,hx⟩,Metric.mem_ball_self (div_pos (hr ⟨x,hx⟩) (by norm_num))⟩)
  let I : ℝ := ∑ i ∈ s, (r i/2)⁻¹
  let B : ℝ := ∑ i ∈ s, A i
  let δ : ℝ := 1/(1+I)
  have hI : 0 ≤ I := Finset.sum_nonneg (fun i hi => inv_nonneg.mpr (div_nonneg (hr i).le (by norm_num)))
  have hB : 0 ≤ B := Finset.sum_nonneg (fun i hi => hA i)
  have hδ : 0 < δ := by dsimp only [δ]; positivity
  have hδi (i : K) (hi : i ∈ s) : δ ≤ r i/2 := by
    have hSingle : (r i/2)⁻¹ ≤ I := Finset.single_le_sum
      (fun j hj => inv_nonneg.mpr (div_nonneg (hr j).le (by norm_num))) hi
    calc
      δ ≤ 1/((r i/2)⁻¹) := one_div_le_one_div_of_le (inv_pos.mpr (div_pos (hr i) (by norm_num))) (by linarith)
      _ = r i/2 := by rw [one_div,inv_inv]
  refine ⟨3+B+2*δ^(-α),by positivity,?_⟩
  intro f P hP hSup hLocal
  have hNear : ∀ p ∈ cylinder K 0 T, ∀ q ∈ cylinder K 0 T,
      ‖p.1-q.1‖ ≤ δ → ‖f p-f q‖ ≤ (B*P)*holderWeight α p q := by
    intro p hp q hq hsp
    obtain ⟨i,hi,hpi⟩ := mem_iUnion₂.mp (hs hp.1)
    have hpNorm : ‖p.1-(i : Space n)‖ < r i/2 := by simpa only [Metric.mem_ball,dist_eq_norm] using hpi
    have hpLocal : p ∈ cylinder (K∩Metric.closedBall (i : Space n) (r i)) 0 T := by
      refine ⟨⟨hp.1,?_⟩,hp.2⟩
      have hh : ‖p.1-(i : Space n)‖ ≤ r i := by linarith [hr i]
      simpa only [Metric.mem_closedBall,dist_eq_norm] using hh
    have hqNorm : ‖q.1-(i : Space n)‖ ≤ r i := by
      have hh := norm_sub_le_norm_sub_add_norm_sub q.1 p.1 (i : Space n)
      rw [norm_sub_rev q.1 p.1] at hh
      linarith [hδi i hi]
    have hqLocal : q ∈ cylinder (K∩Metric.closedBall (i : Space n) (r i)) 0 T :=
      ⟨⟨hq.1,by simpa only [Metric.mem_closedBall,dist_eq_norm] using hqNorm⟩,hq.2⟩
    have hAi : A i ≤ B := Finset.single_le_sum (fun j hj => hA j) hi
    exact ((hLocal i).2.2 p hpLocal q hqLocal).trans
      (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hAi hP)
        (by dsimp only [holderWeight]; positivity))
  have hh := holderBound_of_near_pairs (εx := δ) (εt := 1) hα hP (mul_nonneg hB hP)
    hδ (by norm_num) hSup (fun p hp q hq hsp ht => hNear p hp q hq hsp)
  convert hh using 1
  simp only [Real.one_rpow]
  ring

end Yau.LeafProofs.L16Aux
