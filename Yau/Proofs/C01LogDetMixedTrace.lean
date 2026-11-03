import Yau.Proofs.C01LogDetFirstJets
import Yau.Proofs.C01InverseJets

/-! The actual mixed log-determinant jet is the metric trace of the
curvature matrix already computed from joint positivity. -/

noncomputable section

open scoped Topology ContDiff Matrix ComplexOrder
open Filter

namespace Yau.NodeProofs.C01Aux

open Yau Yau.Blueprint
open Yau.Blueprint.Alignment.Y03Proof

variable {V : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V] {n : ℕ}

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

theorem trace_inverse_curvature_identity (K H₁ H₂ H₁₂ : Herm n) :
    -Matrix.trace (-(K * H₁ * K) * H₂ + K * H₁₂) =
      Matrix.trace (K * (-H₁₂ + H₂ * K * H₁)) := by
  have hcycle : Matrix.trace (K * H₁ * K * H₂) =
      Matrix.trace (K * H₂ * K * H₁) := by
    simpa only [Matrix.mul_assoc] using Matrix.trace_mul_comm (K * H₁) (K * H₂)
  simp only [Matrix.neg_mul, Matrix.trace_add, Matrix.trace_neg, Matrix.mul_add,
    Matrix.mul_neg, ← Matrix.mul_assoc]
  rw [hcycle]
  ring

theorem matrix_logDet_mixed_trace
    (H : V → Herm n) (s : Set V) (hs : IsOpen s)
    (hH : ∀ i j, ContDiffOn ℝ ∞ (fun p => H p i j) s)
    (hpos : ∀ p ∈ s, (H p).PosDef) (z v w : V) (hz : z ∈ s) :
    let K := (H z)⁻¹
    let H₁ : Herm n := fun i j => wirt (fun p => H p i j) z w
    let H₂ : Herm n := fun i j => wirtBar (fun p => H p i j) z v
    let H₁₂ : Herm n := fun i j => wirt (fun p => wirtBar (fun q => H q i j) p v) z w;
    -(wirt (fun p => wirtBar (fun q => (Real.log (H q).det.re : ℂ)) p v) z w) =
      Matrix.trace (K * (-H₁₂ + H₂ * K * H₁)) := by
  dsimp only
  let Hb : V → Herm n := fun p => Matrix.of fun i j => wirtBar (fun q => H q i j) p v
  let A : V → Herm n := fun p => (H p)⁻¹ * Hb p
  have hdet (p : V) (hp : p ∈ s) : (H p).det ≠ 0 :=
    ((hpos p hp).isUnit.map Matrix.detMonoidHom).ne_zero
  have hHm (p : V) (hp : p ∈ s) : DifferentiableAt ℝ H p := by
    change DifferentiableAt ℝ (fun q => Matrix.of.symm (H q)) p
    exact differentiableAt_pi.mpr fun i => differentiableAt_pi.mpr fun j =>
      ((hH i j).contDiffAt (hs.mem_nhds hp)).differentiableAt (by simp)
  have hlog :
      (fun p => wirtBar (fun q => (Real.log (H q).det.re : ℂ)) p v) =ᶠ[𝓝 z]
      (fun p => Matrix.trace (A p)) := by
    filter_upwards [hs.mem_nhds hz] with p hp
    exact (matrix_logDet_wirtinger H s hs hpos p v hp (hHm p hp)).2
  have hKd (i j : Fin n) : DifferentiableAt ℝ (fun p => (H p)⁻¹ i j) z :=
    ((Yau.LeafProofs.SharedCalculus.contDiffOn_matrix_inv hH hdet i j).contDiffAt
      (hs.mem_nhds hz)).differentiableAt (by simp)
  have hBd (i j : Fin n) : DifferentiableAt ℝ (fun p => Hb p i j) z :=
    (wirtBar_contDiffAt (((hH i j).contDiffAt (hs.mem_nhds hz)).of_le
      (by simp)) v).differentiableAt (by norm_num)
  have hAd (i j : Fin n) : DifferentiableAt ℝ (fun p => A p i j) z := by
    change DifferentiableAt ℝ (fun p => ∑ k, (H p)⁻¹ i k * Hb p k j) z
    exact DifferentiableAt.fun_sum (fun k _ => (hKd i k).mul (hBd k j))
  have htrace : wirt (fun p => Matrix.trace (A p)) z w =
      Matrix.trace (Matrix.of fun i j => wirt (fun p => A p i j) z w) := by
    change wirt (fun p => ∑ i, A p i i) z w = ∑ i, wirt (fun p => A p i i) z w
    exact wirt_sum_fn Finset.univ (fun i p => A p i i) (fun i _ => hAd i i) w
  rw [wirt_congr_germ hlog w, htrace]
  have hprod := matrix_wirt_product (fun p => (H p)⁻¹) Hb z w hKd hBd
  change -(Matrix.trace (Matrix.of fun i j =>
    wirt (fun p => ((H p)⁻¹ * Hb p) i j) z w)) = _
  rw [hprod, matrix_inverse_wirt H s hs hH hdet z w hz]
  exact trace_inverse_curvature_identity _ _ _ _

end Yau.NodeProofs.C01Aux
