import Yau.LeafProofs.L16JetExpressions

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000

namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem wordPairingGradientExpr_regular {n : ℕ}
    (g : Yau.RIdx n → Point n → ℝ) (w : List (Yau.RIdx n)) (z : Yau.RIdx n)
    (hg : ∀ j, ContDiff ℝ ∞ (g j)) (hcg : ∀ j, HasCompactSupport (g j)) :
    ∀ t ∈ wordPairingGradientExpr g w z,
      ContDiff ℝ ∞ t.1 ∧ HasCompactSupport t.1 := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨j, _, ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact ⟨hg j, hcg j⟩
    · exact coefficientSpatialWord_regular (hg j) (hcg j) [z]
  · obtain ⟨st, _, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨j, _, ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl
    · exact coefficientSpatialWord_regular (hg j) (hcg j) (z :: st.1)
    · exact coefficientSpatialWord_regular (hg j) (hcg j) st.1

theorem wordPairingGradientExpr_degree {n : ℕ}
    (g : Yau.RIdx n → Point n → ℝ) (w : List (Yau.RIdx n)) (z : Yau.RIdx n) :
    SpatialJetExprDegreeLe (wordPairingGradientExpr g w z) (w.length + 2) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨j, _, ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp only [List.length_cons] <;> omega
  · obtain ⟨st, hst, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨j, _, ht⟩ := List.mem_flatMap.mp ht
    have hLen := commutatorSplits_lower_length w st hst
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
    rcases ht with rfl | rfl <;> simp only [List.length_cons] <;> omega

theorem wordDriftExpr_regular {n : ℕ}
    (c : Point n → Yau.RIdx n → ℝ) (w : List (Yau.RIdx n))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j)) :
    ∀ t ∈ wordDriftExpr c w, ContDiff ℝ ∞ t.1 ∧ HasCompactSupport t.1 := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨j, _, ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_singleton] at ht
    subst t
    exact ⟨hc j, hcc j⟩
  · obtain ⟨st, _, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨j, _, ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_singleton] at ht
    subst t
    exact coefficientSpatialWord_regular (hc j) (hcc j) st.1

theorem wordDriftExpr_degree {n : ℕ}
    (c : Point n → Yau.RIdx n → ℝ) (w : List (Yau.RIdx n)) :
    SpatialJetExprDegreeLe (wordDriftExpr c w) (w.length + 1) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨j, _, ht⟩ := List.mem_flatMap.mp ht
    simp only [List.mem_singleton] at ht
    subst t
    simpa only [List.length_cons] using (le_refl (w.length + 1))
  · obtain ⟨st, hst, ht⟩ := List.mem_flatMap.mp ht
    obtain ⟨j, _, ht⟩ := List.mem_flatMap.mp ht
    have hLen := commutatorSplits_lower_length w st hst
    simp only [List.mem_singleton] at ht
    subst t
    simp only [List.length_cons]
    omega

theorem wordTimeExpr_regular {n : ℕ}
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (w : List (Yau.RIdx n))
    (ha : ∀ q j, ContDiff ℝ ∞ (fun p => a p q j))
    (hca : ∀ q j, HasCompactSupport (fun p => a p q j))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j)) :
    ∀ t ∈ wordTimeExpr a c w, ContDiff ℝ ∞ t.1 ∧ HasCompactSupport t.1 := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨q, _, ht⟩ := List.mem_flatMap.mp ht
    exact wordPairingGradientExpr_regular (fun j p => a p q j) w q (ha q) (hca q) t ht
  · exact wordDriftExpr_regular c w hc hcc t ht

theorem wordTimeExpr_degree {n : ℕ}
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (w : List (Yau.RIdx n)) :
    SpatialJetExprDegreeLe (wordTimeExpr a c w) (w.length + 2) := by
  intro t ht
  rcases List.mem_append.mp ht with ht | ht
  · obtain ⟨q, _, ht⟩ := List.mem_flatMap.mp ht
    exact wordPairingGradientExpr_degree (fun j p => a p q j) w q t ht
  · have hLen := wordDriftExpr_degree c w t ht
    omega

end Yau.LeafProofs.L16Aux
