import Yau.LeafProofs.L16JetExpressionDerivatives
import Yau.LeafProofs.L16JetExpressionBounds
import Yau.LeafProofs.L16ParabolicCoordinates

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

def jointJetExprDerivative {n : ℕ} (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (j : ParabolicJointIdx n) (s : SpatialJetExpr n) : SpatialJetExpr n :=
  match j with
  | .inl i => s.flatMap (spatialJetExprSpatialAtom i)
  | .inr _ => s.flatMap (spatialJetExprTimeAtom a c)

theorem jointJetExprDerivative_tests {n : ℕ} {Q : Set (Point n)}
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (ha : ∀ q j, ContDiff ℝ ∞ (fun p => a p q j))
    (hca : ∀ q j, HasCompactSupport (fun p => a p q j))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (j : ParabolicJointIdx n) (s : SpatialJetExpr n) (hTest : SpatialJetExprTests Q s) :
    SpatialJetExprTests Q (jointJetExprDerivative a c j s) := by
  intro z hz
  cases j with
  | inl i =>
    obtain ⟨t,ht,hz⟩ := List.mem_flatMap.mp hz
    simp only [spatialJetExprSpatialAtom,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl
    · exact test_directionalDerivative (hTest t ht) (Yau.realVec i,0)
    · exact hTest t ht
  | inr i =>
    obtain ⟨t,ht,hz⟩ := List.mem_flatMap.mp hz
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact test_directionalDerivative (hTest t ht) (0,1)
    · obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
      exact test_mul_smooth (hTest t ht) ((wordTimeExpr_regular a c t.2 ha hca hc hcc z' hz').1)

theorem jointJetExprDerivative_degree {n : ℕ}
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (j : ParabolicJointIdx n) (s : SpatialJetExpr n) (M : ℕ) (hDeg : SpatialJetExprDegreeLe s M) :
    SpatialJetExprDegreeLe (jointJetExprDerivative a c j s) (M+2) := by
  intro z hz
  cases j with
  | inl i =>
    obtain ⟨t,ht,hz⟩ := List.mem_flatMap.mp hz
    have hLen := hDeg t ht
    simp only [spatialJetExprSpatialAtom,List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl | rfl <;> simp only [List.length_cons] <;> omega
  | inr i =>
    obtain ⟨t,ht,hz⟩ := List.mem_flatMap.mp hz
    have hLen := hDeg t ht
    rcases List.mem_cons.mp hz with hz | hz
    · subst z
      exact hLen.trans (by omega)
    · obtain ⟨z',hz',rfl⟩ := List.mem_map.mp hz
      have hTimeLen := wordTimeExpr_degree a c t.2 z' hz'
      change z'.2.length ≤ M+2
      omega

def jointJetExpr {n : ℕ} (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (s : SpatialJetExpr n) : List (ParabolicJointIdx n) → SpatialJetExpr n
  | [] => s
  | j::w => jointJetExprDerivative a c j (jointJetExpr a c s w)

theorem jointJetExpr_tests {n : ℕ} {Q : Set (Point n)}
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (ha : ∀ q j, ContDiff ℝ ∞ (fun p => a p q j))
    (hca : ∀ q j, HasCompactSupport (fun p => a p q j))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (s : SpatialJetExpr n) (hTest : SpatialJetExprTests Q s) (w : List (ParabolicJointIdx n)) :
    SpatialJetExprTests Q (jointJetExpr a c s w) := by
  induction w with
  | nil => exact hTest
  | cons j w ih => exact jointJetExprDerivative_tests a c ha hca hc hcc j _ ih

theorem jointJetExpr_degree {n : ℕ}
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (s : SpatialJetExpr n) (M : ℕ) (hDeg : SpatialJetExprDegreeLe s M) (w : List (ParabolicJointIdx n)) :
    SpatialJetExprDegreeLe (jointJetExpr a c s w) (M+2*w.length) := by
  induction w with
  | nil => simpa only [jointJetExpr,List.length_nil,mul_zero,add_zero] using hDeg
  | cons j w ih =>
    have hStep := jointJetExprDerivative_degree a c j _ (M+2*w.length) ih
    convert! hStep using 1

theorem finiteParabolicWeakJet_of_spatial_word_state {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (ha : ∀ q j, ContDiff ℝ ∞ (fun p => a p q j))
    (hca : ∀ q j, HasCompactSupport (fun p => a p q j))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    {u η : Point n → ℝ} (hη : Test Q η) (N : ℕ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (hU0 : U [] = u)
    (hState : WeakSpatialWordState Q a c (2*N+2) U) :
    ∃ J : List (ParabolicJointIdx n) → Point n → ℝ,
      FiniteParabolicWeakJet N (fun p => η p*u p) J := by
  let s : SpatialJetExpr n := [(η,[])]
  have hTest : SpatialJetExprTests Q s := by
    intro t ht
    have ht' : t = (η,[]) := by simpa only [s,List.mem_singleton] using ht
    subst t
    exact hη
  have hDeg : SpatialJetExprDegreeLe s 0 := by
    intro t ht
    have ht' : t = (η,[]) := by simpa only [s,List.mem_singleton] using ht
    subst t
    simp
  let J : List (ParabolicJointIdx n) → Point n → ℝ := fun w => spatialJetExprEval U (jointJetExpr a c s w)
  refine ⟨J,?_,?_,?_⟩
  · funext p
    simp only [J,jointJetExpr,s,spatialJetExprEval,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,
      hU0,add_zero]
  · intro w hw
    apply spatialJetExprEval_memLp_compact hQ U _ (2*w.length)
      (jointJetExpr_tests a c ha hca hc hcc s hTest w)
    · simpa only [zero_add] using jointJetExpr_degree a c s 0 hDeg w
    · intro v hv
      exact hState.1 v (by omega)
  · intro w hw j φ hφ hcφ
    have hTests := jointJetExpr_tests a c ha hca hc hcc s hTest w
    have hDegrees : SpatialJetExprDegreeLe (jointJetExpr a c s w) (2*N+1) := by
      have hD := jointJetExpr_degree a c s 0 hDeg w
      intro t ht
      have hLen := hD t ht
      omega
    have hState' : WeakSpatialWordState Q a c ((2*N+1)+1) U := by
      exact hState
    have hWeak : WeakDirectionalDerivativeOn Set.univ (parabolicJointVec j) (J w) (J (j::w)) := by
      cases j with
      | inl i => exact (spatialJetExprEval_spatial_derivative hQ U (2*N+1) hState'
          _ hTests hDegrees i).2.2.2.2
      | inr i => exact (spatialJetExprEval_time_derivative hQ a c ha hca hc hcc U (2*N+1)
          hState' _ hTests hDegrees).2.2.2.2
    have h := hWeak φ ⟨hφ,hcφ,Set.subset_univ _⟩
    simpa only [Measure.restrict_univ] using h

end Yau.LeafProofs.L16Aux
