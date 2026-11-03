import Yau.Proofs.V01FrameChange
import Yau.Proofs.V01CenterSmooth

/-! The fixed-coordinate majorant is computed from the actual selected
spectral factors and the actual original normalized frame. -/

noncomputable section
open Matrix
open scoped Matrix Topology ContDiff ComplexOrder MatrixOrder
namespace Yau.Blueprint.V01Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem spectralFactor_center_isUnit
    {d : VariationData X q} {j a : ℕ} {δ : ℝ} {F : VariationDisc X}
    {E H Hinv : ℂ → CotangentMatrix n}
    (hSpec : SpectralFactorFor d j a δ F E H Hinv) : IsUnit (H 0) := by
  have hi := hSpec.2.1 0 (by simp)
  let u : (CotangentMatrix n)ˣ :=
    { val := H 0
      inv := Hinv 0
      val_inv := hi.1
      inv_val := hi.2 }
  exact ⟨u, rfl⟩

theorem outerCenter_pos (d : VariationData X q) (j a : ℕ) (F : VariationDisc X) :
    0 < outerCenter d j a F := Real.exp_pos _

def candidateMajorant (d : VariationData X q) (j a : ℕ) (r : ℝ)
    (F : VariationDisc X) (E H : ℂ → CotangentMatrix n) : CotangentMatrix n :=
  fixedPositiveMajorant (H 0) (frameInChart d.chart F.f E 0) r (outerCenter d j a F)

theorem candidateMajorant_properties
    {d : VariationData X q} (hContact : StrictEnvelopeContact d)
    {j a : ℕ} {δ r : ℝ} {F : VariationDisc X} {E H Hinv : ℂ → CotangentMatrix n}
    (hF : AdmissibleVariationDisc d j F) (hE : NormalizedDiscFrame d.G F.f E)
    (hSpec : SpectralFactorFor d j a δ F E H Hinv) (hr : 0 ≤ r)
    (hCenter : (((1 + r : ℝ) : ℂ) • ((H 0)ᴴ * H 0) -
      ((outerCenter d j a F) ^ 2 : ℂ) • centerTestHessian d F E).PosSemidef) :
    (candidateMajorant d j a r F E H).PosDef ∧
    (candidateMajorant d j a r F E H -
      leviMatrix (fun z => d.test (cotangentChartInv d.chart z) F.s)
        (cotangentChart d.chart (F.f 0)) cotangentDir).PosSemidef ∧
    symplecticP (candidateMajorant d j a r F E H) =
      ((1 + r) / (outerCenter d j a F) ^ 2) ^ 2 *
        bivectorCost ((H 0)ᴴ * H 0) (frameBivector (E 0)) := by
  have hChart := (admissible_center_in_chart hF).1
  have hHunit := spectralFactor_center_isUnit hSpec
  have hSunit := frameInChart_isUnit d.chart F.f E 0 hChart (hE.1.1 0 (by simp))
  have hOuter := outerCenter_pos d j a F
  have hTest := center_test_contDiffAt hContact hF
  rw [centerTestHessian_fixed_chart d F E hChart hTest] at hCenter
  refine ⟨fixedPositiveMajorant_posDef hHunit hSunit hr hOuter,
    fixedPositiveMajorant_ge hSunit hOuter
      (by simpa only [Complex.ofReal_pow] using hCenter), ?_⟩
  unfold candidateMajorant
  rw [fixedPositiveMajorant_symplectic_cost hHunit hSunit hr hOuter,
    fixed_frameBivector d.chart F.f E 0 hChart]

end Yau.Blueprint.V01Proof
