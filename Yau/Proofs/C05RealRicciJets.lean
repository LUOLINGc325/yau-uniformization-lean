import Yau.Proofs.C05SingleTraceWord
import Yau.LeafProofs.L23RicciNaturality
import Yau.LeafProofs.L23CurvatureReaction

/-! Actual all-order real Ricci jets are one metric trace of the original
same-order curvature jets. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

def realRicciJet (k : HermitianField M) (c : M.Carrier) :
    (m : ℕ) → ComplexVector n → CovTensor n (2 + m)
  | 0 => ricciTensor k c
  | m + 1 => covariantD k c (realRicciJet k c m)

def realRicciJetNorm (k : HermitianField M) (m : ℕ) (x : M.Carrier) : ℝ :=
  Real.sqrt (covTensorNormSq (realMetricFn k x (chartPt x x))
    (realRicciJet k x m (chartPt x x)))

def ricciTraceWordZero : SingleTraceWord 4 2 where
  toFun := ![Sum.inl 0, Sum.inr 0, Sum.inr 1, Sum.inl 1]
  invFun := Sum.elim (fun p => if p = 0 then 0 else 3) (fun j => if j = 0 then 1 else 2)
  left_inv j := by fin_cases j <;> rfl
  right_inv s := by cases s with
    | inl p => fin_cases p <;> rfl
    | inr j => fin_cases j <;> rfl

def ricciTraceWord : (m : ℕ) → SingleTraceWord (4 + m) (2 + m)
  | 0 => ricciTraceWordZero
  | m + 1 => singleTraceCons (ricciTraceWord m)

theorem realRicciJet_zero_eq_trace (k : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (v : Fin 2 → RIdx n) :
    realRicciJet k c 0 z v = singleTraceEval (ricciTraceWord 0)
      (realMetricFn k c z)⁻¹ (rmJet k c 0 z) v := by
  have hv (a b : RIdx n) :
      (fun j : Fin 4 => Sum.elim ![a, b] v ((ricciTraceWord 0) j)) =
        ![a, v 0, v 1, b] := by
    funext j
    fin_cases j <;> rfl
  unfold singleTraceEval
  simp_rw [hv]
  rfl

set_option backward.isDefEq.respectTransparency false in
theorem realRicciJet_eq_trace (k : HermitianField M) (hk : MetricSmooth k)
    (c : M.Carrier) (m : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (v : Fin (2 + m) → RIdx n) :
    realRicciJet k c m z v = singleTraceEval (ricciTraceWord m)
      (realMetricFn k c z)⁻¹ (rmJet k c m z) v := by
  induction m generalizing z with
  | zero => exact realRicciJet_zero_eq_trace k c z v
  | succ m ih =>
      let i := v 0
      let u : Fin (2 + m) → RIdx n := fun j => v j.succ
      have hv : Fin.cons i u = v := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      rw [← hv]
      have hE : (realRicciJet k c m) =ᶠ[𝓝 z]
          (fun w => singleTraceEval (ricciTraceWord m) (realMetricFn k c w)⁻¹ (rmJet k c m w)) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
        funext v
        exact ih hw v
      have hD := covariantD_eventuallyEq k c _ _ z hE
      have hAd (v : Fin (4 + m) → RIdx n) := ((rmJet_contDiffOn k hk c m v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD k c (realRicciJet k c m) z (Fin.cons i u) = _
      rw [hD, covariantD_singleTraceEval (ricciTraceWord m) k hk c _ hz hAd i u]
      rfl

theorem realRicciJetNorm_le_curvatureJetNorm (k : HermitianField M) (hk : MetricSmooth k)
    (m : ℕ) (x : M.Carrier) :
    realRicciJetNorm k m x ≤ Real.sqrt (2 * n : ℕ) * curvatureJetNorm k m x := by
  have he : realRicciJet k x m (chartPt x x) = singleTraceEval (ricciTraceWord m)
      (realMetricFn k x (chartPt x x))⁻¹ (rmJet k x m (chartPt x x)) := by
    funext v
    exact realRicciJet_eq_trace k hk x m (mem_extChartAt_target x) v
  have hG := Yau.LeafProofs.L12Aux.realMetricFn_posDef k x _ (mem_extChartAt_target x)
  unfold realRicciJetNorm
  rw [he]
  apply (Real.sqrt_le_sqrt (singleTraceEval_normSq_le (ricciTraceWord m) _ hG _)).trans_eq
  rw [Real.sqrt_mul (by positivity)]
  rfl

end Yau.Proofs.C05Aux
