import Yau.Proofs.C05ScalarLaplacianJets
import Yau.Proofs.C05QJetBudgetProduct

/-! Fixed metric traces commute with the actual covariant derivative.
The first two product-jet estimates apply to Ricci compositions. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
open Yau.Proofs.C05QJetBudgetAux
variable {n r s q : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def singleTraceField (w : SingleTraceWord r q) (k : HermitianField M) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (z : ComplexVector n) : CovTensor n q :=
  singleTraceEval w (realMetricFn k c z)⁻¹ (A z)

theorem covariantD_singleTraceField (w : SingleTraceWord r q)
    (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    covariantD k c (singleTraceField w k c A) z =
      singleTraceField (singleTraceCons w) k c (covariantD k c A) z := by
  have hAd (v : Fin r → RIdx n) := ((hA v).contDiffAt
    ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
  funext v
  have hv : Fin.cons (v 0) (fun j => v j.succ) = v := by
    funext j
    exact Fin.cases rfl (fun _ => rfl) j
  rw [← hv]
  exact covariantD_singleTraceEval w k hk c A hz hAd _ _

theorem covariantD_twice_singleTraceField (w : SingleTraceWord r q)
    (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    covariantD k c (covariantD k c (singleTraceField w k c A)) z =
      singleTraceField (singleTraceCons (singleTraceCons w)) k c
        (covariantD k c (covariantD k c A)) z := by
  have he : covariantD k c (singleTraceField w k c A) =ᶠ[𝓝 z]
      singleTraceField (singleTraceCons w) k c (covariantD k c A) := by
    filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with u hu
    exact covariantD_singleTraceField w k hk c A hA hu
  rw [covariantD_eventuallyEq k c _ _ z he]
  exact covariantD_singleTraceField (singleTraceCons w) k hk c _
    (covariantD_contDiffOn k hk c A hA) hz

theorem metricTensorNorm_singleTraceEval_le (w : SingleTraceWord r q)
    (G : Matrix (RIdx n) (RIdx n) ℝ) (hG : G.PosDef) (A : CovTensor n r) :
    metricTensorNorm G (singleTraceEval w G⁻¹ A) ≤
      Real.sqrt (2*n:ℕ) * metricTensorNorm G A := by
  unfold metricTensorNorm
  exact (Real.sqrt_le_sqrt (singleTraceEval_normSq_le w G hG A)).trans_eq
    (Real.sqrt_mul (Nat.cast_nonneg _) _)

theorem covariantD_traceProduct_norm_le (w : SingleTraceWord (r+s) q)
    (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    let G := realMetricFn k c z
    metricTensorNorm G (covariantD k c
      (singleTraceField w k c (fun u => tensorConcatProduct (A u) (B u))) z) ≤
      Real.sqrt (2*n:ℕ) *
        (metricTensorNorm G (covariantD k c A z) * metricTensorNorm G (B z) +
          metricTensorNorm G (A z) * metricTensorNorm G (covariantD k c B z)) := by
  dsimp only
  let G := realMetricFn k c z
  have hG := realMetricFn_posDef k c z hz
  have hAB (v : Fin (r+s) → RIdx n) : ContDiffOn ℝ ∞
      (fun u => tensorConcatProduct (A u) (B u) v) (chartTarget c) := (hA _).mul (hB _)
  rw [covariantD_singleTraceField w k hk c _ hAB hz]
  have hb := covariantD_concatProduct_norm_le k c A B z G hG
    (fun v => ((hA v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp))
    (fun v => ((hB v).contDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp))
  exact (metricTensorNorm_singleTraceEval_le (singleTraceCons w) G hG _).trans
    (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _))

theorem covariantD_twice_traceProduct_norm_le (w : SingleTraceWord (r+s) q)
    (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r) (B : ComplexVector n → CovTensor n s)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c))
    (hB : ∀ v, ContDiffOn ℝ ∞ (fun z => B z v) (chartTarget c))
    {z : ComplexVector n} (hz : z ∈ chartTarget c) :
    let G := realMetricFn k c z
    metricTensorNorm G (covariantD k c (covariantD k c
      (singleTraceField w k c (fun u => tensorConcatProduct (A u) (B u)))) z) ≤
      Real.sqrt (2*n:ℕ) *
        (metricTensorNorm G (covariantD k c (covariantD k c A) z) * metricTensorNorm G (B z) +
          2 * metricTensorNorm G (covariantD k c A z) * metricTensorNorm G (covariantD k c B z) +
          metricTensorNorm G (A z) * metricTensorNorm G (covariantD k c (covariantD k c B) z)) := by
  dsimp only
  let G := realMetricFn k c z
  have hG := realMetricFn_posDef k c z hz
  have hAB (v : Fin (r+s) → RIdx n) : ContDiffOn ℝ ∞
      (fun u => tensorConcatProduct (A u) (B u) v) (chartTarget c) := (hA _).mul (hB _)
  rw [covariantD_twice_singleTraceField w k hk c _ hAB hz]
  have hb := covariantD_twice_product_norm_le k hk c A B hA hB hz G hG
  exact (metricTensorNorm_singleTraceEval_le (singleTraceCons (singleTraceCons w)) G hG _).trans
    (mul_le_mul_of_nonneg_left hb (Real.sqrt_nonneg _))

end Yau.Proofs.C05Aux
