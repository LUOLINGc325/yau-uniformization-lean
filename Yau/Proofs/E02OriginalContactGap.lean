import Yau.Proofs.E02ActualProductGap

open Matrix Set
open scoped Topology Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The ORIGINAL contact tuple has exactly zero actual product gap,
for the SAME B selected before this list of weights. -/
theorem actual_product_gap_at_contacts {n m : ℕ}
    (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (a : ComplexVector n × ℝ) (f : ComplexVector n × ℝ → ℝ)
    (α : Fin m → ℝ) (η : Fin m → ComplexVector n)
    (B : Herm n) (hB : B.PosDef)
    (hGram : weightedColumns α η*(weightedColumns α η)ᴴ = B⁻¹)
    (hEnv : ∀ i, envelopeChart h T x (a.1,η i,a.2) = 1)
    (hSum : ∑ i, α i = n) (hf : f a = Real.log B.det.re) (θ : ℝ) :
    actualProductGap X h T x f α (rowProjector (weightedColumns α η)) θ (a.1,a.2,η) = 0 := by
  have hM : (weightedColumns α η*(weightedColumns α η)ᴴ).PosDef := by
    rw [hGram]
    exact hB.inv
  have hWeighted : (∑ i, α i*chartEnvelopeReal X h T x (a.1,η i,a.2)) = n := by
    simpa only [chartEnvelopeReal,hEnv,EReal.toReal_one,mul_one] using hSum
  have hPenalty : projectorPenalty (n := n) (rowProjector (weightedColumns α η))
      (weightedColumns α η) = 0 :=
    (projectorPenalty_nonneg_eq_zero _ _ hM hM).2.mpr rfl
  have hSupport := (trace_logdet_support_eq_iff
    (weightedColumns α η*(weightedColumns α η)ᴴ) B hM hB).mpr hGram
  have hTrace : (Matrix.trace (B*(weightedColumns α η*(weightedColumns α η)ᴴ))).re = n := by
    rw [hGram,Matrix.mul_nonsing_inv _ (hB.isUnit.map Matrix.detMonoidHom),Matrix.trace_one]
    simp
  rw [hTrace] at hSupport
  change (∑ i, α i*chartEnvelopeReal X h T x (a.1,η i,a.2))-
    ((n:ℝ)+f a+logGram (weightedColumns α η)-
      θ*projectorPenalty (n := n) (rowProjector (weightedColumns α η)) (weightedColumns α η)) = 0
  rw [hWeighted,hf,hPenalty,mul_zero,sub_zero]
  unfold logGram
  linarith

end Yau.NodeProofs.E02Aux
