import Yau.LeafProofs.L21CompactCommutator

/-! The genuine compact weighted energies in the corrected basic identity. -/

open scoped ContDiff
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {n : ℕ} {O : Set (X n)}

def coreScalarEnergy (φ : X n → ℝ) (v : Fin n → CompactTest O) : ℝ :=
  ∑ i, weightedScalarEnergy φ (v i)

def coreGradientEnergy (hO : IsOpen O) {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A O) (φ : X n → ℝ) (v : Fin n → CompactTest O) : ℝ :=
  ∑ i, ∑ j, weightedScalarEnergy φ (testD hO hA i (v j))

def compactFormQ (hO : IsOpen O) {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A O) {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    (v : Fin n → CompactTest O) : ℝ :=
  weightedScalarEnergy φ ((∑ i, testDs hO hA hφ i (v i)) : CompactTest O) +
    (1 / 2 : ℝ) * ∑ i, ∑ j,
      weightedScalarEnergy φ ((testD hO hA i (v j) - testD hO hA j (v i)) : CompactTest O)

def coreLeviEnergy (hO : IsOpen O) {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A O) {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O)
    {d : Fin n → Fin n → Fin n → X n → ℂ}
    (hd : ∀ i j k, ContDiffOn ℝ ∞ (d i j k) O) (v : Fin n → CompactTest O) : ℝ :=
  ∑ i, ∑ j, testPair φ (v i) (multiplyLocalTest hO (contDiffOn_correctedLevi hO hA hφ hd i j) (v j))

theorem coreGradientEnergy_nonneg (hO : IsOpen O) {A : X n → Matrix (Fin n) (Fin n) ℂ}
    (hA : MatrixSmoothOn A O) (φ : X n → ℝ) (v : Fin n → CompactTest O) :
    0 ≤ coreGradientEnergy hO hA φ v :=
  Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => weightedScalarEnergy_nonneg φ _

theorem coreScalarEnergy_nonneg (φ : X n → ℝ) (v : Fin n → CompactTest O) :
    0 ≤ coreScalarEnergy φ v := Finset.sum_nonneg fun i _ => weightedScalarEnergy_nonneg φ _

theorem weighted_basic_identity_core (hO : IsOpen O)
    {A : X n → Matrix (Fin n) (Fin n) ℂ} (hA : MatrixSmoothOn A O)
    {φ : X n → ℝ} (hφ : ContDiffOn ℝ ∞ φ O) (v : Fin n → CompactTest O) :
    compactFormQ hO hA hφ v = coreGradientEnergy hO hA φ v +
      ∑ i, ∑ j, testPair φ (v i)
        (testD hO hA i (testDs hO hA hφ j (v j)) - testDs hO hA hφ j (testD hO hA i (v j))) := by
  simpa only [compactFormQ, coreGradientEnergy, testPair_self_eq_weightedScalarEnergy hO hφ] using
    weighted_basic_identity_on_compact_tests hO hA hφ v

end Yau.LeafProofs.L21Aux
