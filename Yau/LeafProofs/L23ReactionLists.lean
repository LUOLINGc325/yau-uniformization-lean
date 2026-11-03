import Yau.LeafProofs.L23JetTermCalculus
import Yau.LeafProofs.L23ReactionBaseWords
import Yau.LeafProofs.L23ReactionCorrectionWords

/-! The finite reaction list, its exact numerical recurrence, and the
norm bound supplied by its genuine two-contraction terms. -/

noncomputable section
open scoped Matrix

namespace Yau.LeafProofs.L23Aux
set_option backward.isDefEq.respectTransparency false

def correctionTerm0 (k : ℕ) : JetTerm (k+1) where
  leftOrder := 0
  rightOrder := k+1
  coeff := .negHalf
  word := correctionWord0 (4+k)

def correctionTerm1 (k : ℕ) (s : Fin (4+k)) : JetTerm (k+1) where
  leftOrder := 0
  rightOrder := k+1
  coeff := .negOne
  word := correctionWord1 s

def correctionTerm2 (k : ℕ) (s : Fin (4+k)) : JetTerm (k+1) where
  leftOrder := 1
  rightOrder := k
  coeff := .posHalf
  word := correctionWord2 s

def extraTerms (k : ℕ) : List (JetTerm (k+1)) :=
  correctionTerm0 k :: (List.ofFn (correctionTerm1 k)++List.ofFn (correctionTerm2 k))

def reactionTerms : (k : ℕ) → List (JetTerm k)
  | 0 => baseTerms
  | k+1 => (reactionTerms k).flatMap (fun e => [e.dLeft,e.dRight])++extraTerms k

theorem extraTerms_length (k : ℕ) : (extraTerms k).length=2*k+9 := by
  simp [extraTerms]
  omega

theorem derivativeTerms_length {k : ℕ} (L : List (JetTerm k)) :
    (L.flatMap (fun e => [e.dLeft,e.dRight])).length=2*L.length := by
  induction L with
  | nil => simp
  | cons e L ih => simp [ih]; omega

theorem reactionTerms_length (k : ℕ) : (reactionTerms k).length=reactionTermCount k := by
  induction k with
  | zero => exact baseTerms_length
  | succ k ih =>
      rw [reactionTerms,List.length_append,derivativeTerms_length,extraTerms_length,ih]
      rfl

variable {n k : ℕ} {M : ComplexManifold n}

def jetTermListEval (L : List (JetTerm k)) (h : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) : CovTensor n (4+k) :=
  fun v => (L.map (fun e => e.eval h c z v)).sum

def reactionListEval (h : HermitianField M) (c : M.Carrier) (k : ℕ)
    (z : ComplexVector n) : CovTensor n (4+k) := jetTermListEval (reactionTerms k) h c z

theorem jetTermListEval_nil (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n) :
    jetTermListEval ([] : List (JetTerm k)) h c z=0 := rfl

theorem jetTermListEval_cons (e : JetTerm k) (L : List (JetTerm k))
    (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n) :
    jetTermListEval (e::L) h c z=e.eval h c z+jetTermListEval L h c z := rfl

theorem jetTermListEval_append (L R : List (JetTerm k))
    (h : HermitianField M) (c : M.Carrier) (z : ComplexVector n) :
    jetTermListEval (L++R) h c z=jetTermListEval L h c z+jetTermListEval R h c z := by
  funext v
  simp [jetTermListEval,List.map_append,List.sum_append]

theorem jetTermListEval_norm_le (L : List (JetTerm k))
    (h : HermitianField M) (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    Real.sqrt (covTensorNormSq (realMetricFn h c z) (jetTermListEval L h c z)) ≤
      (L.length : ℝ)*((2*n : ℕ)*jetConvolution h c k z) := by
  induction L with
  | nil => simp [jetTermListEval_nil,sqrt_covTensorNormSq_zero]
  | cons e L ih =>
      rw [jetTermListEval_cons]
      calc
        _≤Real.sqrt (covTensorNormSq (realMetricFn h c z) (e.eval h c z))+
            Real.sqrt (covTensorNormSq (realMetricFn h c z) (jetTermListEval L h c z)) :=
          sqrt_covTensorNormSq_add_le _ (L12Aux.realMetricFn_posDef h c z hz) _ _
        _≤(2*n : ℕ)*jetConvolution h c k z+(L.length : ℝ)*((2*n : ℕ)*jetConvolution h c k z) :=
          add_le_add (e.eval_norm_le_convolution h c hz) ih
        _=_ := by simp only [List.length_cons,Nat.cast_add,Nat.cast_one]; ring

theorem reactionListEval_norm_le (h : HermitianField M) (c : M.Carrier)
    (k : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    Real.sqrt (covTensorNormSq (realMetricFn h c z) (reactionListEval h c k z)) ≤
      (2*n : ℕ)*(reactionTermCount k : ℝ)*jetConvolution h c k z := by
  have hh := jetTermListEval_norm_le (reactionTerms k) h c hz
  rw [reactionTerms_length] at hh
  change Real.sqrt (covTensorNormSq (realMetricFn h c z) (jetTermListEval (reactionTerms k) h c z))≤_
  nlinarith [hh]

end Yau.LeafProofs.L23Aux
