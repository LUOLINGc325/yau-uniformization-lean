import Yau.Proofs.C05ScalarJetDefinitions
import Yau.LeafProofs.L23ContractionWordCalculus
import Yau.LeafProofs.L23ContractionWordNorm
import Yau.Proofs.G01RicciNormalization

/-! The actual scalar covariant jets are one-half a fixed two-trace word in
the same-order original Riemann curvature jets. -/

noncomputable section
open scoped Manifold Topology ContDiff

namespace Yau.Proofs.C05Aux
open Yau Yau.LeafProofs.L23Aux
variable {n : ℕ} {M : ComplexManifold n}

def scalarTraceWordZero : Word2 4 0 0 where
  wire :=
    { toFun := Sum.elim (fun i => Sum.inr (![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩] i)) Fin.elim0
      invFun := Sum.elim Fin.elim0 (fun p => Sum.inl
        (if p.1 = 0 then if p.2 = 0 then 1 else 2 else if p.2 = 0 then 0 else 3))
      left_inv := by
        intro s
        cases s with
        | inl i => fin_cases i <;> rfl
        | inr i => exact Fin.elim0 i
      right_inv := by
        intro s
        cases s with
        | inl i => exact Fin.elim0 i
        | inr p => rcases p with ⟨i, j⟩; fin_cases i <;> fin_cases j <;> rfl }

def scalarTraceWord : (m : ℕ) → Word2 (4 + m) 0 m
  | 0 => scalarTraceWordZero
  | m + 1 => (scalarTraceWord m).dLeft

theorem scalarTraceWord_zero_eval (k : HermitianField M) (c : M.Carrier)
    (z : ComplexVector n) (v : Fin 0 → RIdx n) :
    (scalarTraceWord 0).eval (realMetricFn k c z)⁻¹ (rmTensor k c z) (fun _ => 1) v =
      Yau.Blueprint.realScalarCurvatureInChart k c z := by
  rw [Word2.eval_quad]
  have hv (a b d e : RIdx n) :
      (fun j : Fin 4 => Sum.elim v (pairAssignment a b d e)
        ((scalarTraceWord 0).wire (Sum.inl j))) = ![d, a, b, e] := by
    funext j
    fin_cases j <;> rfl
  simp_rw [hv]
  simp only [mul_one]
  have hR (a b : RIdx n) : realRicciCoeff k c z a b =
      ∑ d : RIdx n, ∑ e : RIdx n, (realMetricFn k c z)⁻¹ d e *
        rmTensor k c z ![d, a, b, e] := rfl
  unfold Yau.Blueprint.realScalarCurvatureInChart
  simp_rw [hR]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  apply Finset.sum_congr rfl
  intro d _
  apply Finset.sum_congr rfl
  intro e _
  ring

theorem word_eval_zero_right {r s q : ℕ} (w : Word2 r s q)
    (H : Matrix (RIdx n) (RIdx n) ℝ) (A : CovTensor n r) (v : Fin q → RIdx n) :
    w.eval H A (0 : CovTensor n s) v = 0 := by
  simp [Word2.eval]

theorem covariantD_scalar_one (k : HermitianField M) (c : M.Carrier) (z : ComplexVector n) :
    covariantD k c (fun _ (_ : Fin 0 → RIdx n) => (1 : ℝ)) z = 0 := by
  ext v
  simp [covariantD, rDeriv]

set_option backward.isDefEq.respectTransparency false in
theorem scalarJet_eq_curvature_trace_word (k : HermitianField M) (hk : MetricSmooth k)
    (hK : KahlerClosed k) (c : M.Carrier) (m : ℕ) {z : ComplexVector n}
    (hz : z ∈ chartTarget c) (v : Fin m → RIdx n) :
    scalarJet k (scalarCurvature k) c m z v =
      (1 / 2 : ℝ) * (scalarTraceWord m).eval (realMetricFn k c z)⁻¹
        (rmJet k c m z) (fun _ => 1) v := by
  induction m generalizing z with
  | zero =>
      change scalarCurvature k (chartInv c z) =
        (1 / 2 : ℝ) * (scalarTraceWord 0).eval (realMetricFn k c z)⁻¹
          (rmTensor k c z) (fun _ => 1) v
      rw [scalarTraceWord_zero_eval]
      have hs := Yau.NodeProofs.G01Aux.realScalarCurvatureInChart_eq k hk hK c z hz
      change scalarCurvature k (chartInv c z) = _
      linarith
  | succ m ih =>
      let i := v 0
      let u : Fin m → RIdx n := fun j => v j.succ
      have hv : Fin.cons i u = v := by
        funext j
        exact Fin.cases rfl (fun _ => rfl) j
      rw [← hv]
      have hE : (scalarJet k (scalarCurvature k) c m) =ᶠ[𝓝 z]
          (fun w v => (1 / 2 : ℝ) * (scalarTraceWord m).eval (realMetricFn k c w)⁻¹
            (rmJet k c m w) (fun _ => 1) v) := by
        filter_upwards [(isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz] with w hw
        funext v
        exact ih hw v
      have hD := covariantD_eventuallyEq k c _ _ z hE
      have hA := rmJet_contDiffOn k hk c m
      have hB : ∀ v : Fin 0 → RIdx n,
          ContDiffOn ℝ ∞ (fun _ : ComplexVector n => (1 : ℝ)) (chartTarget c) :=
        fun _ => contDiffOn_const
      have hF := Word2.eval_contDiffOn (scalarTraceWord m) k hk c
        (rmJet k c m) (fun _ _ => 1) hA hB
      have hFd (v : Fin m → RIdx n) := ((hF v).contDiffAt
        ((isOpen_extChartAt_target (I := ComplexModel n) c).mem_nhds hz)).differentiableAt (by simp)
      have hDc := covariantD_const_mul_at k c
        (fun w => (scalarTraceWord m).eval (realMetricFn k c w)⁻¹ (rmJet k c m w) (fun _ => 1))
        z hFd (1 / 2)
      have hW := Word2.covariantD_eval (scalarTraceWord m) k hk c
        (rmJet k c m) (fun _ _ => 1) hA hB hz i u
      rw [covariantD_scalar_one, word_eval_zero_right, add_zero] at hW
      change covariantD k c (scalarJet k (scalarCurvature k) c m) z (Fin.cons i u) = _
      rw [hD, hDc]
      change (1 / 2 : ℝ) * _ = _
      rw [hW]
      rfl

end Yau.Proofs.C05Aux
