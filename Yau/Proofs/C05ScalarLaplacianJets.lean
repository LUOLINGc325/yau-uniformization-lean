import Yau.Proofs.C05IntrinsicJetCoordinates
import Yau.Proofs.C05SingleTraceWord
import Yau.Proofs.G04ScalarNormalization
import Yau.LeafProofs.L23TensorNormLinear

/-! Every scalar covariant derivative of the actual complex Laplacian
is one-half the same metric trace of the scalar jet two orders higher. -/
noncomputable section
open Filter
open scoped Topology Manifold ContDiff Matrix
namespace Yau.Proofs.C05Aux
open Yau Blueprint Yau.Proofs.C05GradientFlowAux Yau.Proofs.C05HessianPropagationAux
open Yau.LeafProofs.L12Aux Yau.LeafProofs.L23Aux
variable {n r q : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false

def scalarLapTraceWordZero : SingleTraceWord 2 0 where
  toFun := Sum.inl
  invFun := Sum.elim id Fin.elim0
  left_inv _ := rfl
  right_inv s := by cases s with | inl _ => rfl | inr j => exact Fin.elim0 j

def scalarLapTraceWord : (m : ℕ) → SingleTraceWord (2+m) m
  | 0 => scalarLapTraceWordZero
  | m+1 => singleTraceCons (scalarLapTraceWord m)

theorem singleTraceEval_contDiffOn (w : SingleTraceWord r q)
    (k : HermitianField M) (hk : MetricSmooth k) (c : M.Carrier)
    (A : ComplexVector n → CovTensor n r)
    (hA : ∀ v, ContDiffOn ℝ ∞ (fun z => A z v) (chartTarget c)) (v : Fin q → RIdx n) :
    ContDiffOn ℝ ∞ (fun z => singleTraceEval w (realMetricFn k c z)⁻¹ (A z) v)
      (chartTarget c) := by
  apply ContDiffOn.sum
  intro a _
  apply ContDiffOn.sum
  intro b _
  exact (Yau.LeafProofs.L23Aux.realMetricFn_inverse_contDiffOn k hk c a b).mul (hA _)

theorem scalarLapTraceWord_zero_eval (k : HermitianField M) (f : M.Carrier → ℝ)
    (c : M.Carrier) (z : ComplexVector n) (v : Fin 0 → RIdx n) :
    singleTraceEval (scalarLapTraceWord 0) (realMetricFn k c z)⁻¹ (scalarJet k f c 2 z) v =
      realLaplacianInChart k c f z := by
  have hv (a b : RIdx n) :
      (fun j : Fin 2 => Sum.elim ![a,b] v ((scalarLapTraceWord 0) j)) = ![a,b] := by
    funext j
    fin_cases j <;> rfl
  unfold singleTraceEval
  simp_rw [hv,scalarJet_two]
  rfl

theorem scalarJet_laplacian_trace (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (c : M.Carrier) (m : ℕ) {z : ComplexVector n} (hz : z ∈ chartTarget c)
    (v : Fin m → RIdx n) :
    scalarJet k (laplacian k f) c m z v = (1/2:ℝ) *
      singleTraceEval (scalarLapTraceWord m) (realMetricFn k c z)⁻¹
        (scalarJet k f c (2+m) z) v := by
  induction m generalizing z with
  | zero =>
      change laplacian k f (chartInv c z) = _
      rw [scalarLapTraceWord_zero_eval]
      have he := Yau.NodeProofs.G04Aux.scalarLaplacian k hk hK f hf c z hz
      linarith
  | succ m ih =>
      let i := v 0
      let u : Fin m → RIdx n := fun j => v j.succ
      have hv : Fin.cons i u = v := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      rw [← hv]
      have hE : scalarJet k (laplacian k f) c m =ᶠ[𝓝 z]
          (fun w v => (1/2:ℝ) * singleTraceEval (scalarLapTraceWord m)
            (realMetricFn k c w)⁻¹ (scalarJet k f c (2+m) w) v) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
        funext v
        exact ih hw v
      have hA := scalarJet_contDiffOn k hk f hf c (2+m)
      have hF := singleTraceEval_contDiffOn (scalarLapTraceWord m) k hk c _ hA
      have hFd (v : Fin m → RIdx n) := ((hF v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      have hAd (v : Fin (2+m) → RIdx n) := ((hA v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      change covariantD k c (scalarJet k (laplacian k f) c m) z (Fin.cons i u) = _
      rw [covariantD_eventuallyEq k c _ _ z hE,
        covariantD_const_mul_at k c _ z hFd]
      change (1/2:ℝ) * _ = _
      rw [covariantD_singleTraceEval (scalarLapTraceWord m) k hk c _ hz hAd i u]
      rfl

theorem scalarJetNorm_laplacian_le (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (f : M.Carrier → ℝ) (hf : SmoothFn f)
    (m : ℕ) (x : M.Carrier) :
    scalarJetNorm k (laplacian k f) m x ≤
      (Real.sqrt (2*n:ℕ) / 2) * scalarJetNorm k f (2+m) x := by
  let G := realMetricFn k x (chartPt x x)
  let A := scalarJet k f x (2+m) (chartPt x x)
  have hG := realMetricFn_posDef k x (chartPt x x) (mem_extChartAt_target x)
  have he : scalarJet k (laplacian k f) x m (chartPt x x) =
      fun v => (1/2:ℝ) * singleTraceEval (scalarLapTraceWord m) G⁻¹ A v := by
    funext v
    exact scalarJet_laplacian_trace k hk hK f hf x m (mem_extChartAt_target x) v
  have hn := singleTraceEval_normSq_le (scalarLapTraceWord m) G hG A
  have hh : Real.sqrt (covTensorNormSq G (singleTraceEval (scalarLapTraceWord m) G⁻¹ A)) ≤
      Real.sqrt (2*n:ℕ) * Real.sqrt (covTensorNormSq G A) := by
    exact (Real.sqrt_le_sqrt hn).trans_eq (Real.sqrt_mul (Nat.cast_nonneg _) _)
  unfold scalarJetNorm
  rw [he,sqrt_covTensorNormSq_const_mul]
  calc
    _ ≤ (1/2:ℝ) * (Real.sqrt (2*n:ℕ) * Real.sqrt (covTensorNormSq G A)) := by
      norm_num only [abs_of_pos (by norm_num : (0:ℝ)<1/2)]
      exact mul_le_mul_of_nonneg_left hh (by norm_num)
    _ = _ := by dsimp only [G,A]; ring

end Yau.Proofs.C05Aux
