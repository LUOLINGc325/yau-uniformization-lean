import Yau.Proofs.C05RicciSquareJetsLists

/-! The same genuine two-trace Leibniz calculation for arbitrary tensor fields. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciSquareJetsAux.Generic
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n r s q m : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def jet (k : HermitianField M) (c : M.Carrier) (A : ComplexVector n → CovTensor n r) :
    (m : ℕ) → ComplexVector n → CovTensor n (r+m)
  | 0 => A
  | m+1 => covariantD k c (jet k c A m)

theorem jet_contDiffOn (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (m : ℕ) (v : Fin (r+m) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => jet k c A m z v) (chartTarget c) := by
  induction m with
  | zero => exact hA v
  | succ m ih => exact covariantD_contDiffOn k hk c _ ih v

structure Term (r s q m : ℕ) where
  leftOrder : ℕ
  rightOrder : ℕ
  word : Word2 (r+leftOrder) (s+rightOrder) (q+m)

namespace Term

def dLeft (e : Term r s q m) : Term r s q (m+1) where
  leftOrder := e.leftOrder+1
  rightOrder := e.rightOrder
  word := e.word.dLeft

def dRight (e : Term r s q m) : Term r s q (m+1) where
  leftOrder := e.leftOrder
  rightOrder := e.rightOrder+1
  word := e.word.dRight

def eval (e : Term r s q m) (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (z : ComplexVector n) : CovTensor n (q+m) :=
  e.word.eval (realMetricFn k c z)⁻¹ (jet k c A e.leftOrder z) (jet k c B e.rightOrder z)

theorem total (e : Term r s q m) (w : Word2 r s q) : e.leftOrder+e.rightOrder=m := by
  have h := Fintype.card_congr e.word.wire
  have h0 := Fintype.card_congr w.wire
  simp only [SlotLabel,PairLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at h h0
  omega

theorem contDiffOn (e : Term r s q m) (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c)) (v : Fin (q+m) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => e.eval k c A B z v) (chartTarget c) :=
  e.word.eval_contDiffOn k hk c _ _ (jet_contDiffOn k hk c A hA e.leftOrder)
    (jet_contDiffOn k hk c B hB e.rightOrder) v

theorem covariantD_eval (e : Term r s q m) (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    covariantD k c (e.eval k c A B) z = e.dLeft.eval k c A B z + e.dRight.eval k c A B z := by
  funext v
  change covariantD k c (fun u => e.word.eval (realMetricFn k c u)⁻¹
    (jet k c A e.leftOrder u) (jet k c B e.rightOrder u)) z v = _
  have H := e.word.covariantD_eval k hk c _ _ (jet_contDiffOn k hk c A hA e.leftOrder)
    (jet_contDiffOn k hk c B hB e.rightOrder) hz (v 0) (Fin.tail v)
  simpa only [eval,dLeft,dRight,jet,Fin.cons_self_tail,Pi.add_apply] using H

theorem norm_le (e : Term r s q m) (w : Word2 r s q) (hm : m ≤ 3)
    (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    {z : ComplexVector n} (hz : z ∈ chartTarget c) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hA : ∀ j ≤ 3, metricTensorNorm (realMetricFn k c z) (jet k c A j z) ≤ CA)
    (hB : ∀ j ≤ 3, metricTensorNorm (realMetricFn k c z) (jet k c B j z) ≤ CB) :
    metricTensorNorm (realMetricFn k c z) (e.eval k c A B z) ≤ (2*n:ℕ)*CA*CB := by
  have hl : e.leftOrder ≤ 3 := by have h := e.total w; omega
  have hr : e.rightOrder ≤ 3 := by have h := e.total w; omega
  have H := e.word.eval_norm_le (realMetricFn k c z) (realMetricFn_posDef k c z hz)
    (jet k c A e.leftOrder z) (jet k c B e.rightOrder z)
  have hp := mul_le_mul (hA _ hl) (hB _ hr)
    (metricTensorNorm_nonneg (realMetricFn k c z) (jet k c B e.rightOrder z)) hCA
  change metricTensorNorm _ (e.eval k c A B z) ≤
    (2*n:ℕ)*metricTensorNorm _ (jet k c A e.leftOrder z)*metricTensorNorm _ (jet k c B e.rightOrder z) at H
  calc
    _ ≤ _ := H
    _ = (2*n:ℕ)*(metricTensorNorm (realMetricFn k c z) (jet k c A e.leftOrder z)*
      metricTensorNorm (realMetricFn k c z) (jet k c B e.rightOrder z)) := by ring
    _ ≤ (2*n:ℕ)*(CA*CB) := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)
    _ = _ := by ring

end Term

def derivativeList (l : List (Term r s q m)) : List (Term r s q (m+1)) :=
  l.flatMap (fun e => [e.dLeft,e.dRight])

def terms (w : Word2 r s q) : (m : ℕ) → List (Term r s q m)
  | 0 => [⟨0,0,w⟩]
  | m+1 => derivativeList (terms w m)

def evalTerms (l : List (Term r s q m)) (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (z : ComplexVector n) : CovTensor n (q+m) := (l.map (fun e => e.eval k c A B z)).sum

theorem derivativeList_length (l : List (Term r s q m)) :
    (derivativeList l).length = 2*l.length := by
  induction l with
  | nil => simp [derivativeList]
  | cons e l ih =>
      simp only [derivativeList,List.flatMap_cons,List.length_append,List.length_cons,List.length_nil] at *
      omega

theorem terms_length (w : Word2 r s q) (m : ℕ) : (terms w m).length = 2^m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [terms,derivativeList_length,ih,pow_succ]; omega

theorem evalTerms_contDiffOn (l : List (Term r s q m)) (k : HermitianField M)
    (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c)) (v : Fin (q+m) → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => evalTerms l k c A B z v) (chartTarget c) := by
  induction l with
  | nil => exact contDiffOn_const
  | cons e l ih => simpa only [evalTerms,List.map_cons,List.sum_cons,Pi.add_apply] using
      (e.contDiffOn k hk c A B hA hB v).add ih

theorem covariantD_evalTerms (l : List (Term r s q m)) (k : HermitianField M)
    (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    covariantD k c (evalTerms l k c A B) z = evalTerms (derivativeList l) k c A B z := by
  induction l with
  | nil => funext v; simp [evalTerms,derivativeList,covariantD,rDeriv]
  | cons e l ih =>
      have he (v : Fin (q+m) → RIdx n) := ((e.contDiffOn k hk c A B hA hB v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      have hl (v : Fin (q+m) → RIdx n) := ((evalTerms_contDiffOn l k hk c A B hA hB v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD k c (fun u => e.eval k c A B u + evalTerms l k c A B u) z = _
      rw [covariantD_add_at k c _ _ z he hl,e.covariantD_eval k hk c A B hA hB hz,ih]
      simp [derivativeList,evalTerms,List.map_append,List.sum_append,add_assoc]

theorem jet_word_eval (w : Word2 r s q) (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    (m : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    jet k c (fun u => w.eval (realMetricFn k c u)⁻¹ (A u) (B u)) m z =
      evalTerms (terms w m) k c A B z := by
  induction m generalizing z with
  | zero => simp [jet,terms,evalTerms,Term.eval]
  | succ m ih =>
      have he : jet k c (fun u => w.eval (realMetricFn k c u)⁻¹ (A u) (B u)) m =ᶠ[𝓝 z]
          (evalTerms (terms w m) k c A B) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with u hu
        exact ih hu
      change covariantD k c _ z = _
      rw [covariantD_eventuallyEq k c _ _ z he,covariantD_evalTerms _ k hk c A B hA hB hz]
      rfl

theorem word_covariantJet_norm_le_three (w : Word2 r s q) (k : HermitianField M)
    (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) {CA CB : ℝ} (hCA : 0 ≤ CA) (hCB : 0 ≤ CB)
    (hJA : ∀ j ≤ 3, metricTensorNorm (realMetricFn k c z) (jet k c A j z) ≤ CA)
    (hJB : ∀ j ≤ 3, metricTensorNorm (realMetricFn k c z) (jet k c B j z) ≤ CB)
    (m : ℕ) (hm : m ≤ 3) :
    metricTensorNorm (realMetricFn k c z)
      (jet k c (fun u => w.eval (realMetricFn k c u)⁻¹ (A u) (B u)) m z) ≤
        8 * (2*n:ℕ) * CA * CB := by
  have hl (l : List (Term r s q m)) :
      metricTensorNorm (realMetricFn k c z) (evalTerms l k c A B z) ≤
        (l.length:ℝ)*(2*n:ℕ)*CA*CB := by
    induction l with
    | nil => simp [evalTerms,metricTensorNorm,sqrt_covTensorNormSq_zero]
    | cons e l ih =>
        have H := sqrt_covTensorNormSq_add_le (realMetricFn k c z) (realMetricFn_posDef k c z hz)
          (e.eval k c A B z) (evalTerms l k c A B z)
        change metricTensorNorm _ (_ + _) ≤ metricTensorNorm _ _ + metricTensorNorm _ _ at H
        calc
          _ ≤ _ := H
          _ ≤ (2*n:ℕ)*CA*CB+(l.length:ℝ)*(2*n:ℕ)*CA*CB :=
            add_le_add (e.norm_le w hm k c A B hz hCA hCB hJA hJB) ih
          _ = _ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring
  rw [jet_word_eval w k hk c A B hA hB m hz]
  have hc : ((terms w m).length:ℝ) ≤ 8 := by rw [terms_length]; interval_cases m <;> norm_num
  have H := mul_le_mul_of_nonneg_right hc
    (mul_nonneg (mul_nonneg (Nat.cast_nonneg (2*n)) hCA) hCB)
  exact (hl (terms w m)).trans (by simpa only [mul_assoc] using H)

end Yau.Proofs.C05RicciSquareJetsAux.Generic
