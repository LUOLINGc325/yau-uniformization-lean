import Yau.Proofs.C05IntrinsicJetCoordinates
import Yau.LeafProofs.L23ContractionWordCalculus
import Yau.LeafProofs.L23ContractionWordNorm
import Yau.LeafProofs.L23TensorNormLinear

/-! Finite actual two-trace terms. The order identity is forced by the wiring. -/
noncomputable section
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05RicciSquareJetsAux
open Yau Yau.Proofs.C05Aux Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

structure RicciTerm (m : ℕ) where
  leftOrder : ℕ
  rightOrder : ℕ
  word : Word2 (2 + leftOrder) (2 + rightOrder) m

namespace RicciTerm
variable {m : ℕ}

theorem total (e : RicciTerm m) : e.leftOrder + e.rightOrder = m := by
  have h := Fintype.card_congr e.word.wire
  simp only [SlotLabel,PairLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin] at h
  omega

def dLeft (e : RicciTerm m) : RicciTerm (m + 1) where
  leftOrder := e.leftOrder + 1
  rightOrder := e.rightOrder
  word := e.word.dLeft

def dRight (e : RicciTerm m) : RicciTerm (m + 1) where
  leftOrder := e.leftOrder
  rightOrder := e.rightOrder + 1
  word := e.word.dRight

def eval (e : RicciTerm m) (k : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) : CovTensor n m :=
  e.word.eval (realMetricFn k c z)⁻¹
    (realRicciJet k c e.leftOrder z) (realRicciJet k c e.rightOrder z)

theorem contDiffOn (e : RicciTerm m) (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (v : Fin m → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => e.eval k c z v) (chartTarget c) :=
  e.word.eval_contDiffOn k hk c _ _ (realRicciJet_contDiffOn k hk c e.leftOrder)
    (realRicciJet_contDiffOn k hk c e.rightOrder) v

theorem covariantD_eval (e : RicciTerm m) (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    covariantD k c (e.eval k c) z = e.dLeft.eval k c z + e.dRight.eval k c z := by
  funext v
  change covariantD k c (fun u => e.word.eval (realMetricFn k c u)⁻¹
    (realRicciJet k c e.leftOrder u) (realRicciJet k c e.rightOrder u)) z v = _
  have H := e.word.covariantD_eval k hk c _ _
    (realRicciJet_contDiffOn k hk c e.leftOrder)
    (realRicciJet_contDiffOn k hk c e.rightOrder) hz (v 0) (Fin.tail v)
  simpa only [eval,dLeft,dRight,realRicciJet,Fin.cons_self_tail,Pi.add_apply] using H

theorem norm_le (e : RicciTerm m) {N : ℕ} (hm : m ≤ N) (k : HermitianField M)
    (x : M.Carrier) {B : ℝ} (hB : 0 ≤ B)
    (hR : ∀ j ≤ N, realRicciJetNorm k j x ≤ B) :
    metricTensorNorm (realMetricFn k x (chartPt x x)) (e.eval k x (chartPt x x)) ≤
      (2 * n : ℕ) * B ^ 2 := by
  have hleft : e.leftOrder ≤ N := by have ht := e.total; omega
  have hright : e.rightOrder ≤ N := by have ht := e.total; omega
  have H := e.word.eval_norm_le (realMetricFn k x (chartPt x x))
    (realMetricFn_posDef k x _ (mem_extChartAt_target x))
    (realRicciJet k x e.leftOrder (chartPt x x))
    (realRicciJet k x e.rightOrder (chartPt x x))
  change metricTensorNorm _ (e.eval k x (chartPt x x)) ≤
    (2*n:ℕ) * realRicciJetNorm k e.leftOrder x * realRicciJetNorm k e.rightOrder x at H
  have hn : 0 ≤ realRicciJetNorm k e.rightOrder x := Real.sqrt_nonneg _
  have hp : realRicciJetNorm k e.leftOrder x * realRicciJetNorm k e.rightOrder x ≤ B ^ 2 := by
    rw [pow_two]
    exact mul_le_mul (hR _ hleft) (hR _ hright) hn hB
  calc
    _ ≤ (2*n:ℕ) * realRicciJetNorm k e.leftOrder x * realRicciJetNorm k e.rightOrder x := H
    _ = (2*n:ℕ) * (realRicciJetNorm k e.leftOrder x * realRicciJetNorm k e.rightOrder x) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hp (Nat.cast_nonneg _)

end RicciTerm
end Yau.Proofs.C05RicciSquareJetsAux
