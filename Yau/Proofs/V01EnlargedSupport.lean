import Yau.Proofs.V01SupportSchur
import Yau.Proofs.V01ParentOrder

/-! The actual V04 enlargement is performed before V02 and V03 are
instantiated. The entire inner witness uses that single enlarged data set. -/

noncomputable section
open scoped Matrix ContDiff ComplexOrder MatrixOrder
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem schur_witness_of_variation_setup
    (hSchur : SymplecticSchur n) (hD05 : DiscFramesContract X.manifold)
    (hV02 : V02Contract X) (hV03 : V03Contract X) (hV04 : V04Contract X)
    (d : VariationData X q) (hd : VariationSetup d)
    {φ : ComplexVector n × ComplexVector n × ℝ → ℝ}
    (p : ComplexVector n × ComplexVector n × ℝ) (hφ : ContDiffAt ℝ 2 φ p)
    (α : ℝ) (hα : 0 < α)
    (hTest : d.test = chartTest d.chart (canonicalQuadraticSupport φ p α))
    (hPoint : contactAssoc d.contact = p)
    (hC : (leviMatrix (fun z : CotangentCoord n => φ (z.1, z.2, p.2.2))
      (p.1, p.2.1) cotangentDir - (α : ℂ) • (1 : CotangentMatrix n)).toBlocks₂₂.PosDef) :
    let W := leviMatrix (fun z : CotangentCoord n => φ (z.1, z.2, p.2.2))
      (p.1, p.2.1) cotangentDir - (α : ℂ) • (1 : CotangentMatrix n)
    ∃ K : Herm n, K.PosSemidef ∧ (K - schurComplement W).PosSemidef ∧
      (W.toBlocks₂₂ᵀ * K).trace.re ≤ coordinateTimeSlope φ p := by
  obtain ⟨k, B, a, _hB, hdB, _hCuts, _ha, hReg, hLoc, _hSym, _hDefReal,
    _hFejer, _hFreq, hNeg, hCenter, hSpec, hClock, _hBackward, hPos, hSub⟩ :=
    exists_enlarged_variation_estimates hV02 hV03 hV04 d hd
  let db : VariationData X q := {d with B := B}
  have hG : CotangentImmersion db.G := hdB.2.2.2.2.1
  have hContact : StrictEnvelopeContact db := hdB.2.2.2.2.2.2.2.1
  exact quadratic_support_schur_witness db k a hSchur hD05 hG hContact hReg hLoc
    hCenter hNeg hSpec hClock hPos hSub p hφ α hα hTest hPoint hC

end Yau.Blueprint.V01Proof
