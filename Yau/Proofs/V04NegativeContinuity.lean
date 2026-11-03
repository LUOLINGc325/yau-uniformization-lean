import Yau.Proofs.V04HilbertClipping

/-! Clipping is continuous on actual Hermitian families in the Euclidean
space of entries. No regularity of a chosen eigenbasis is used. -/

open scoped Topology ComplexOrder MatrixOrder
noncomputable section
namespace Yau.Blueprint.V04Proof
open Yau Yau.Blueprint

variable {n : ℕ}

theorem matrixNegative_entry_continuous {α : Type*} [TopologicalSpace α]
    {A : α → CotangentMatrix n} (hA : ∀ i k, Continuous (fun x => A x i k))
    (hHerm : ∀ x, (A x).IsHermitian) (i k : CotangentIndex n) :
    Continuous (fun x => matrixNegative (A x) i k) := by
  let S := {v : EuclideanSpace ℂ (CotangentIndex n × CotangentIndex n) //
    Matrix.IsHermitian ((fun i k => v (i, k)) : CotangentMatrix n)}
  let Q : S → EuclideanSpace ℂ (CotangentIndex n × CotangentIndex n) :=
    fun v => cotangentMatrixHS (matrixNegative (fun i k => v.1 (i, k)))
  have hQ : LipschitzWith 1 Q := by
    apply LipschitzWith.of_dist_le_mul
    intro v w
    change dist (cotangentMatrixHS (matrixNegative (fun i k => v.1 (i, k))))
      (cotangentMatrixHS (matrixNegative (fun i k => w.1 (i, k)))) ≤
        (1 : ℝ) * dist v.1 w.1
    simp only [one_mul, dist_eq_norm]
    exact matrixNegative_HS_nonexpansive _ _ v.2 w.2
  let f : α → S := fun x => ⟨cotangentMatrixHS (A x), hHerm x⟩
  have hf : Continuous f := by
    apply Continuous.subtype_mk
    exact (PiLp.continuous_toLp 2 _).comp (continuous_pi (fun p => hA p.1 p.2))
  have hcomp : Continuous (fun x => Q (f x)) := hQ.continuous.comp hf
  exact (PiLp.continuous_apply (p := (2 : ENNReal))
    (β := fun _ : CotangentIndex n × CotangentIndex n => ℂ) (i, k)).comp hcomp

theorem matrixNegative_trace_pow_continuous {α : Type*} [TopologicalSpace α]
    {A : α → CotangentMatrix n} (hA : ∀ i k, Continuous (fun x => A x i k))
    (hHerm : ∀ x, (A x).IsHermitian) (p : ℕ) :
    Continuous (fun x => (Matrix.trace (matrixNegative (A x) ^ p)).re) := by
  have hN : Continuous (fun x => matrixNegative (A x)) :=
    continuous_pi (fun i => continuous_pi (fun k => matrixNegative_entry_continuous hA hHerm i k))
  apply Complex.continuous_re.comp
  unfold Matrix.trace
  apply continuous_finsetSum
  intro i _
  exact ((hN.pow p).matrix_elem i i)

end Yau.Blueprint.V04Proof
