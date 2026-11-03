import Yau.LeafProofs.L16JetExpressions

open MeasureTheory Filter
open scoped Topology ContDiff
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem weakDirectionalDerivativeOn_add {n : ℕ} {Q : Set (Point n)}
    {u v z t : Point n → ℝ} {e : Point n}
    (hu : MemLp u 2 (volume.restrict Q)) (hv : MemLp v 2 (volume.restrict Q))
    (hz : MemLp z 2 (volume.restrict Q)) (ht : MemLp t 2 (volume.restrict Q))
    (hU : WeakDirectionalDerivativeOn Q e u z) (hV : WeakDirectionalDerivativeOn Q e v t) :
    WeakDirectionalDerivativeOn Q e (fun p => u p+v p) (fun p => z p+t p) := by
  intro φ hφ
  have hDφ := test_memLp (test_directionalDerivative hφ e)
  have hφ2 := test_memLp hφ
  have hSplit1 := integral_add (hu.integrable_mul hDφ) (hv.integrable_mul hDφ)
  have hSplit2 := integral_add (hz.integrable_mul hφ2) (ht.integrable_mul hφ2)
  simp only [Pi.mul_apply] at hSplit1 hSplit2
  simp_rw [add_mul]
  rw [hSplit1,hSplit2,hU φ hφ,hV φ hφ]
  ring

theorem spatialJetExprEval_weak_derivative_flatMap {n : ℕ}
    (U : List (Yau.RIdx n) → Point n → ℝ) (s : SpatialJetExpr n)
    (D : ((Point n → ℝ) × List (Yau.RIdx n)) → SpatialJetExpr n) (e : Point n)
    (hAtom : ∀ t ∈ s,
      MemLp (fun p => t.1 p*U t.2 p) 2 volume ∧ HasCompactSupport (fun p => t.1 p*U t.2 p) ∧
      MemLp (spatialJetExprEval U (D t)) 2 volume ∧ HasCompactSupport (spatialJetExprEval U (D t)) ∧
      WeakDirectionalDerivativeOn Set.univ e (fun p => t.1 p*U t.2 p) (spatialJetExprEval U (D t))) :
    MemLp (spatialJetExprEval U s) 2 volume ∧ HasCompactSupport (spatialJetExprEval U s) ∧
      MemLp (spatialJetExprEval U (s.flatMap D)) 2 volume ∧ HasCompactSupport (spatialJetExprEval U (s.flatMap D)) ∧
      WeakDirectionalDerivativeOn Set.univ e (spatialJetExprEval U s) (spatialJetExprEval U (s.flatMap D)) := by
  induction s with
  | nil =>
    refine ⟨MemLp.zero',HasCompactSupport.zero,MemLp.zero',HasCompactSupport.zero,?_⟩
    intro φ hφ
    simp only [spatialJetExprEval,List.flatMap_nil,List.map_nil,List.sum_nil,zero_mul,integral_zero,neg_zero]
  | cons t s ih =>
    have hH := hAtom t List.mem_cons_self
    have hT := ih (fun z hz => hAtom z (List.mem_cons_of_mem _ hz))
    have hLeft : spatialJetExprEval U (t::s) = fun p => t.1 p*U t.2 p+spatialJetExprEval U s p := rfl
    have hRight : spatialJetExprEval U ((t::s).flatMap D) =
        fun p => spatialJetExprEval U (D t) p+spatialJetExprEval U (s.flatMap D) p := by
      funext p
      rw [List.flatMap_cons,spatialJetExprEval_append]
    rw [hLeft,hRight]
    refine ⟨?_,hH.2.1.add hT.2.1,?_,hH.2.2.2.1.add hT.2.2.2.1,?_⟩
    · convert! hH.1.add hT.1 using 1
    · convert! hH.2.2.1.add hT.2.2.1 using 1
    · apply weakDirectionalDerivativeOn_add
      · simpa only [Measure.restrict_univ] using hH.1
      · simpa only [Measure.restrict_univ] using hT.1
      · simpa only [Measure.restrict_univ] using hH.2.2.1
      · simpa only [Measure.restrict_univ] using hT.2.2.1
      · exact hH.2.2.2.2
      · exact hT.2.2.2.2

def spatialJetExprSpatialAtom {n : ℕ} (i : Yau.RIdx n)
    (t : (Point n → ℝ) × List (Yau.RIdx n)) : SpatialJetExpr n :=
  [((fun p => fderiv ℝ t.1 p (Yau.realVec i,0)),t.2),(t.1,i::t.2)]

def spatialJetExprTimeAtom {n : ℕ} (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (t : (Point n → ℝ) × List (Yau.RIdx n)) : SpatialJetExpr n :=
  ((fun p => fderiv ℝ t.1 p (0,1)),t.2)::
    ((wordTimeExpr a c t.2).map (fun z => ((fun p => t.1 p*z.1 p),z.2)))

theorem spatialJetExprSpatialAtom_eval {n : ℕ} (i : Yau.RIdx n)
    (U : List (Yau.RIdx n) → Point n → ℝ)
    (t : (Point n → ℝ) × List (Yau.RIdx n)) (p : Point n) :
    spatialJetExprEval U (spatialJetExprSpatialAtom i t) p =
      t.1 p*U (i::t.2) p+U t.2 p*fderiv ℝ t.1 p (Yau.realVec i,0) := by
  simp only [spatialJetExprSpatialAtom,spatialJetExprEval,List.map_cons,List.sum_cons,List.map_nil,
    List.sum_nil,add_zero]
  ring

theorem spatialJetExprTimeAtom_eval {n : ℕ} (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (U : List (Yau.RIdx n) → Point n → ℝ)
    (t : (Point n → ℝ) × List (Yau.RIdx n)) (p : Point n) :
    spatialJetExprEval U (spatialJetExprTimeAtom a c t) p =
      t.1 p*weakWordTime a c U t.2 p+U t.2 p*fderiv ℝ t.1 p (0,1) := by
  change fderiv ℝ t.1 p (0,1)*U t.2 p+
    spatialJetExprEval U ((wordTimeExpr a c t.2).map (fun z => ((fun p => t.1 p*z.1 p),z.2))) p = _
  rw [spatialJetExprEval_scale,wordTimeExpr_eval]
  ring

theorem spatialJetExprEval_spatial_derivative {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ}
    (U : List (Yau.RIdx n) → Point n → ℝ) (k : ℕ)
    (hState : WeakSpatialWordState Q a c (k+1) U)
    (s : SpatialJetExpr n) (hTest : SpatialJetExprTests Q s) (hDeg : SpatialJetExprDegreeLe s k)
    (i : Yau.RIdx n) :
    MemLp (spatialJetExprEval U s) 2 volume ∧ HasCompactSupport (spatialJetExprEval U s) ∧
      MemLp (spatialJetExprEval U (s.flatMap (spatialJetExprSpatialAtom i))) 2 volume ∧
      HasCompactSupport (spatialJetExprEval U (s.flatMap (spatialJetExprSpatialAtom i))) ∧
      WeakDirectionalDerivativeOn Set.univ (Yau.realVec i,0)
        (spatialJetExprEval U s) (spatialJetExprEval U (s.flatMap (spatialJetExprSpatialAtom i))) := by
  apply spatialJetExprEval_weak_derivative_flatMap
  intro t ht
  have hData := weakDirectionalDerivativeOn_cutoff hQ (hState.1 t.2 (by have h := hDeg t ht; omega))
    (hState.1 (i::t.2) (by have h := hDeg t ht; simp only [List.length_cons]; omega))
    (weakGradientOn_directional (hState.2.1 t.2 (by have h := hDeg t ht; omega)) i) (hTest t ht)
  have hFun : spatialJetExprEval U (spatialJetExprSpatialAtom i t) =
      fun p => t.1 p*U (i::t.2) p+U t.2 p*fderiv ℝ t.1 p (Yau.realVec i,0) :=
    funext (fun p => spatialJetExprSpatialAtom_eval i U t p)
  rw [hFun]
  exact hData

theorem spatialJetExprEval_time_derivative {n : ℕ} {Q : Set (Point n)} (hQ : IsOpen Q)
    (a : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ)
    (ha : ∀ q j, ContDiff ℝ ∞ (fun p => a p q j))
    (hca : ∀ q j, HasCompactSupport (fun p => a p q j))
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (U : List (Yau.RIdx n) → Point n → ℝ) (k : ℕ)
    (hState : WeakSpatialWordState Q a c (k+1) U)
    (s : SpatialJetExpr n) (hTest : SpatialJetExprTests Q s) (hDeg : SpatialJetExprDegreeLe s k) :
    MemLp (spatialJetExprEval U s) 2 volume ∧ HasCompactSupport (spatialJetExprEval U s) ∧
      MemLp (spatialJetExprEval U (s.flatMap (spatialJetExprTimeAtom a c))) 2 volume ∧
      HasCompactSupport (spatialJetExprEval U (s.flatMap (spatialJetExprTimeAtom a c))) ∧
      WeakDirectionalDerivativeOn Set.univ (0,1)
        (spatialJetExprEval U s) (spatialJetExprEval U (s.flatMap (spatialJetExprTimeAtom a c))) := by
  apply spatialJetExprEval_weak_derivative_flatMap
  intro t ht
  have hTw := weakWordTime_weak_derivative hQ a c ha hca hc hcc U k hState t.2 (hDeg t ht)
  have hData := weakDirectionalDerivativeOn_cutoff hQ (hState.1 t.2 (by have h := hDeg t ht; omega))
    hTw.1 hTw.2 (hTest t ht)
  have hFun : spatialJetExprEval U (spatialJetExprTimeAtom a c t) =
      fun p => t.1 p*weakWordTime a c U t.2 p+U t.2 p*fderiv ℝ t.1 p (0,1) :=
    funext (fun p => spatialJetExprTimeAtom_eval a c U t p)
  rw [hFun]
  exact hData

end Yau.LeafProofs.L16Aux
