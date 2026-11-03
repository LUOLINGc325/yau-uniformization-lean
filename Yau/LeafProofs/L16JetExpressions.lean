import Yau.LeafProofs.L16WeakWordTime

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 3000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

abbrev SpatialJetExpr (n : ℕ) := List ((Point n → ℝ) × List (Yau.RIdx n))

def spatialJetExprEval {n : ℕ} (U : List (Yau.RIdx n) → Point n → ℝ)
    (s : SpatialJetExpr n) (p : Point n) : ℝ :=
  (s.map (fun t => t.1 p*U t.2 p)).sum

def SpatialJetExprTests {n : ℕ} (Q : Set (Point n)) (s : SpatialJetExpr n) : Prop :=
  ∀ t ∈ s, Test Q t.1

def SpatialJetExprDegreeLe {n : ℕ} (s : SpatialJetExpr n) (M : ℕ) : Prop :=
  ∀ t ∈ s, t.2.length ≤ M

theorem spatialJetExprEval_append {n : ℕ} (U : List (Yau.RIdx n) → Point n → ℝ)
    (s t : SpatialJetExpr n) (p : Point n) :
    spatialJetExprEval U (s++t) p = spatialJetExprEval U s p+spatialJetExprEval U t p := by
  simp only [spatialJetExprEval,List.map_append,List.sum_append]

theorem spatialJetExprEval_flatMap {n : ℕ} {ι : Type*} (U : List (Yau.RIdx n) → Point n → ℝ)
    (xs : List ι) (f : ι → SpatialJetExpr n) (p : Point n) :
    spatialJetExprEval U (xs.flatMap f) p = (xs.map (fun i => spatialJetExprEval U (f i) p)).sum := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    rw [List.flatMap_cons,spatialJetExprEval_append,ih]
    rfl

theorem spatialJetExprEval_finsetFlatMap {n : ℕ} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (U : List (Yau.RIdx n) → Point n → ℝ) (f : ι → SpatialJetExpr n) (p : Point n) :
    spatialJetExprEval U (Finset.univ.toList.flatMap f) p = ∑ i, spatialJetExprEval U (f i) p := by
  rw [spatialJetExprEval_flatMap,Finset.sum_map_toList]

theorem spatialJetExprEval_scale {n : ℕ} (U : List (Yau.RIdx n) → Point n → ℝ)
    (s : SpatialJetExpr n) (η : Point n → ℝ) (p : Point n) :
    spatialJetExprEval U (s.map (fun t => ((fun p => η p*t.1 p),t.2))) p =
      η p*spatialJetExprEval U s p := by
  induction s with
  | nil => simp only [spatialJetExprEval,List.map_nil,List.sum_nil,mul_zero]
  | cons t s ih =>
    simp only [List.map_cons,spatialJetExprEval,List.sum_cons] at ih ⊢
    rw [ih]
    ring

theorem spatialJetExprEval_memLp_compact {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (U : List (Yau.RIdx n) → Point n → ℝ) (s : SpatialJetExpr n) (M : ℕ)
    (hTest : SpatialJetExprTests Q s) (hDeg : SpatialJetExprDegreeLe s M)
    (hU : ∀ w, w.length ≤ M → MemLp (U w) 2 (volume.restrict Q)) :
    MemLp (spatialJetExprEval U s) 2 volume ∧ HasCompactSupport (spatialJetExprEval U s) := by
  induction s with
  | nil => exact ⟨MemLp.zero',HasCompactSupport.zero⟩
  | cons t s ih =>
    have hs := ih (fun z hz => hTest z (List.mem_cons_of_mem _ hz))
      (fun z hz => hDeg z (List.mem_cons_of_mem _ hz))
    have hHead := test_mul_memLp_global hQ (hTest t List.mem_cons_self) (hU t.2 (hDeg t List.mem_cons_self))
    have hcHead : HasCompactSupport (fun p => t.1 p*U t.2 p) := (hTest t List.mem_cons_self).2.1.mul_right
    constructor
    · convert! hHead.add hs.1 using 1
    · exact hcHead.add hs.2

def wordPairingGradientExpr {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (w : List (Yau.RIdx n)) (z : Yau.RIdx n) : SpatialJetExpr n :=
  (Finset.univ.toList.flatMap (fun j => [(g j,z::j::w),(coefficientSpatialWord [z] (g j),j::w)]))++
    ((commutatorSplits w).flatMap (fun st => Finset.univ.toList.flatMap (fun j =>
      [(coefficientSpatialWord (z::st.1) (g j),j::st.2),
       (coefficientSpatialWord st.1 (g j),j::z::st.2)])))

theorem wordPairingGradientExpr_eval {n : ℕ} (g : Yau.RIdx n → Point n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (z : Yau.RIdx n) (p : Point n) :
    spatialJetExprEval U (wordPairingGradientExpr g w z) p = weakWordPairingGradient g U w p z := by
  have hMain : spatialJetExprEval U (Finset.univ.toList.flatMap (fun j : Yau.RIdx n =>
      [(g j,z::j::w),(coefficientSpatialWord [z] (g j),j::w)])) p =
      ∑ j, (g j p*U (z::j::w) p+U (j::w) p*fderiv ℝ (g j) p (Yau.realVec z,0)) := by
    rw [spatialJetExprEval_finsetFlatMap]
    apply Finset.sum_congr rfl
    intro j _
    simp only [spatialJetExprEval,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,
      coefficientSpatialWord,add_zero]
    ring
  have hSplit (st : List (Yau.RIdx n) × List (Yau.RIdx n)) :
      spatialJetExprEval U (Finset.univ.toList.flatMap (fun j : Yau.RIdx n =>
        [(coefficientSpatialWord (z::st.1) (g j),j::st.2),
         (coefficientSpatialWord st.1 (g j),j::z::st.2)])) p =
        weakWordCorrection g U (z::st.1) st.2 p+weakWordCorrection g U st.1 (z::st.2) p := by
    rw [spatialJetExprEval_finsetFlatMap]
    simp only [spatialJetExprEval,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero,
      weakWordCorrection,Finset.sum_add_distrib]
  rw [wordPairingGradientExpr,spatialJetExprEval_append,hMain,spatialJetExprEval_flatMap]
  simp_rw [hSplit]
  rfl

def wordDriftExpr {n : ℕ} (c : Point n → Yau.RIdx n → ℝ) (w : List (Yau.RIdx n)) : SpatialJetExpr n :=
  (Finset.univ.toList.flatMap (fun j => [(fun p => c p j,j::w)]))++
    ((commutatorSplits w).flatMap (fun st => Finset.univ.toList.flatMap (fun j =>
      [(coefficientSpatialWord st.1 (fun p => c p j),j::st.2)])))

theorem wordDriftExpr_eval {n : ℕ} (c : Point n → Yau.RIdx n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (p : Point n) :
    spatialJetExprEval U (wordDriftExpr c w) p = weakWordDrift c U w p := by
  rw [wordDriftExpr,spatialJetExprEval_append,spatialJetExprEval_finsetFlatMap,spatialJetExprEval_flatMap]
  simp only [spatialJetExprEval,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero]
  unfold weakWordDrift weakWordSource
  congr 1
  apply congrArg List.sum
  apply List.map_congr_left
  intro st _
  change spatialJetExprEval U (Finset.univ.toList.flatMap (fun j : Yau.RIdx n =>
    [(coefficientSpatialWord st.1 (fun p => c p j),j::st.2)])) p = _
  rw [spatialJetExprEval_finsetFlatMap]
  simp only [spatialJetExprEval,List.map_cons,List.sum_cons,List.map_nil,List.sum_nil,add_zero,
    weakWordCorrection]

def wordTimeExpr {n : ℕ} (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (w : List (Yau.RIdx n)) : SpatialJetExpr n :=
  (Finset.univ.toList.flatMap (fun q => wordPairingGradientExpr (fun j p => a p q j) w q))++wordDriftExpr c w

theorem wordTimeExpr_eval {n : ℕ} (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ) (w : List (Yau.RIdx n)) (p : Point n) :
    spatialJetExprEval U (wordTimeExpr a c w) p = weakWordTime a c U w p := by
  rw [wordTimeExpr,spatialJetExprEval_append,spatialJetExprEval_finsetFlatMap,wordDriftExpr_eval]
  simp_rw [wordPairingGradientExpr_eval]
  rfl

end Yau.LeafProofs.L16Aux
