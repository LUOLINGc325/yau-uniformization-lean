import Yau.Proofs.C05RicciSquareJetsBase
import Yau.LeafProofs.L23TensorLocalAlgebra

/-! Actual finite Leibniz sums: every differentiation doubles the term list. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciSquareJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n m : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def derivativeList (l : List (RicciTerm m)) : List (RicciTerm (m + 1)) :=
  l.flatMap (fun e => [e.dLeft,e.dRight])

def ricciSquareTerms : (m : ℕ) → List (RicciTerm m)
  | 0 => [ricciSquareTermZero]
  | m + 1 => derivativeList (ricciSquareTerms m)

def evalTerms (l : List (RicciTerm m)) (k : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) : CovTensor n m := (l.map (fun e => e.eval k c z)).sum

theorem evalTerms_nil (k : HermitianField M) (c : M.Carrier) (z : ComplexVector n) :
    evalTerms ([] : List (RicciTerm m)) k c z = 0 := rfl

theorem evalTerms_cons (e : RicciTerm m) (l : List (RicciTerm m))
    (k : HermitianField M) (c : M.Carrier) (z : ComplexVector n) :
    evalTerms (e :: l) k c z = e.eval k c z + evalTerms l k c z := rfl

theorem derivativeList_length (l : List (RicciTerm m)) :
    (derivativeList l).length = 2 * l.length := by
  induction l with
  | nil => simp [derivativeList]
  | cons e l ih =>
      simp only [derivativeList,List.flatMap_cons,List.length_append,List.length_cons,
        List.length_nil] at *
      omega

theorem ricciSquareTerms_length (m : ℕ) : (ricciSquareTerms m).length = 2 ^ m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [ricciSquareTerms,derivativeList_length,ih,pow_succ]; omega

theorem evalTerms_contDiffOn (l : List (RicciTerm m)) (k : HermitianField M)
    (hk : MetricSmooth k) (c : M.Carrier) (v : Fin m → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => evalTerms l k c z v) (chartTarget c) := by
  induction l with
  | nil => exact contDiffOn_const
  | cons e l ih =>
      simpa only [evalTerms_cons,Pi.add_apply] using (e.contDiffOn k hk c v).add ih

theorem covariantD_evalTerms (l : List (RicciTerm m)) (k : HermitianField M)
    (hk : MetricSmooth k) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    covariantD k c (evalTerms l k c) z = evalTerms (derivativeList l) k c z := by
  induction l with
  | nil =>
      funext v
      simp [evalTerms,derivativeList,covariantD,rDeriv]
  | cons e l ih =>
      have he (v : Fin m → RIdx n) := ((e.contDiffOn k hk c v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      have hl (v : Fin m → RIdx n) := ((evalTerms_contDiffOn l k hk c v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD k c (fun w => e.eval k c w + evalTerms l k c w) z = _
      rw [covariantD_add_at k c _ _ z he hl,e.covariantD_eval k hk c hz,ih]
      simp [derivativeList,evalTerms,List.map_append,List.sum_append,add_assoc]

theorem evalTerms_norm_le (l : List (RicciTerm m)) {N : ℕ} (hm : m ≤ N)
    (k : HermitianField M) (x : M.Carrier) {B : ℝ} (hB : 0 ≤ B)
    (hR : ∀ j ≤ N, realRicciJetNorm k j x ≤ B) :
    metricTensorNorm (realMetricFn k x (chartPt x x)) (evalTerms l k x (chartPt x x)) ≤
      (l.length : ℝ) * (2 * n : ℕ) * B ^ 2 := by
  induction l with
  | nil => simp [evalTerms,metricTensorNorm,sqrt_covTensorNormSq_zero]
  | cons e l ih =>
      rw [evalTerms_cons]
      have H := sqrt_covTensorNormSq_add_le (realMetricFn k x (chartPt x x))
        (realMetricFn_posDef k x _ (mem_extChartAt_target x))
        (e.eval k x (chartPt x x)) (evalTerms l k x (chartPt x x))
      change metricTensorNorm _ (_ + _) ≤ metricTensorNorm _ _ + metricTensorNorm _ _ at H
      calc
        _ ≤ _ := H
        _ ≤ (2*n:ℕ) * B^2 + (l.length:ℝ) * (2*n:ℕ) * B^2 :=
          add_le_add (e.norm_le hm k x hB hR) ih
        _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

end Yau.Proofs.C05RicciSquareJetsAux
