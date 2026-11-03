import Yau.Proofs.E02EnvelopeV01Test
import Yau.Proofs.E02SchurEpsilon

open Matrix Set Filter
open scoped Topology ContDiff Manifold Matrix ComplexOrder
noncomputable section
namespace Yau.NodeProofs.E02Aux
open Yau Yau.Blueprint

/-- The original V01 ancestor yields an epsilon-free PSD majorant at a
FIXED κ-contact. Its source is the actual attained interior source of the
original envelope's compact inf-convolution. -/
theorem attained_source_jet_majorant {n : ℕ}
    (X : KahlerManifold n) (h : Flow X) (hV : EnvelopeInequality X h)
    (T : ℝ) (x : Pt X)
    (K : Set (EuclideanSpace ℝ (Fin (4*n+1))))
    (hDom : ∀ q ∈ K, (envelopeRealCoordinates n).symm q ∈ envelopeDomain X T x)
    {κ : ℝ} (hκ : 0 < κ) (q : EuclideanSpace ℝ (Fin (4*n+1)))
    (a : ComplexVector n × ComplexVector n × ℝ)
    (ha : envelopeRealCoordinates n a ∈ interior K)
    (hMin : compactInfConvolution K (packedEnvelopeReal X h T x) κ q =
      packedEnvelopeReal X h T x (envelopeRealCoordinates n a)+
        ‖q-envelopeRealCoordinates n a‖^2/(2*κ))
    (p : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (A : EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ]
      EuclideanSpace ℝ (Fin (4*n+1)) →L[ℝ] ℝ)
    (hJet : RealSecondJet (compactInfConvolution K (packedEnvelopeReal X h T x) κ) q p A)
    (hC : (cotangentTensor A).toBlocks₂₂.PosDef) :
    ∃ L : Herm n, L.PosSemidef ∧ (L-schurComplement (cotangentTensor A)).PosSemidef ∧
      (Matrix.trace ((cotangentTensor A).toBlocks₂₂ᵀ*L)).re ≤
        p (envelopeRealCoordinates n (0,0,1)) := by
  apply exists_psd_majorant_remove_epsilon (cotangentTensor A)
    (p (envelopeRealCoordinates n (0,0,1))) hC
  intro ε hε hShift
  exact attained_source_V01_test X h hV T x K hDom hκ q a ha hMin p A hJet hε hShift

end Yau.NodeProofs.E02Aux
