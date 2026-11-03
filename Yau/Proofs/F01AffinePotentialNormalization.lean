import Yau.Proofs.F01SchauderScalarMultiplication
import Yau.Proofs.F01PotentialSpatialLinearization
import Yau.Proofs.F01ComplexLeviFrobenius

/-! Affine parabolic normalization with the genuine inverse-square
potential amplitude. The native Levi matrix and one-sided clock equation
are unchanged under this simultaneous space-time transformation. -/
noncomputable section
open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Parabolic
variable {n : ℕ}

def affineParabolicPotential (ρ : ℝ) (c : Space n) (τ : ℝ) (u : Point n → ℝ) : Point n → ℝ :=
  fun p => (ρ ^ 2)⁻¹ * affineParabolicPullback ρ c τ u p

theorem spatialDD_affineParabolicPotential {ρ : ℝ} (hρ : ρ ≠ 0)
    (c : Space n) (τ : ℝ) (u : Point n → ℝ) (p : Point n) :
    spatialDD (affineParabolicPotential ρ c τ u) p =
      spatialDD u (affineParabolicPoint ρ c τ p) := by
  unfold affineParabolicPotential
  rw [spatialDD_real_smul, spatialDD_affineParabolicPullback, smul_smul,
    inv_mul_cancel₀ (pow_ne_zero 2 hρ), one_smul]

theorem timeD_affineParabolicPotential {S O : Set (Space n)}
    {l r a b ρ τ : ℝ} {c : Space n} {u : Point n → ℝ}
    (hρ : ρ ≠ 0) (hab : a < b) (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r))
    {p : Point n} (hp : p ∈ cylinder O a b) :
    timeD (cylinder O a b) (affineParabolicPotential ρ c τ u) p =
      timeD (cylinder S l r) u (affineParabolicPoint ρ c τ p) := by
  unfold affineParabolicPotential
  rw [timeD_real_mul, timeD_affineParabolicPullback hab hu hSpace hClock hp,
    ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 2 hρ), one_mul]

theorem c2_affineParabolicPotential {S O : Set (Space n)}
    {l r a b ρ τ : ℝ} {c : Space n} {u : Point n → ℝ}
    (hab : a < b) (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r)) :
    C2 (cylinder O a b) (affineParabolicPotential ρ c τ u) :=
  Yau.LeafProofs.L16Aux.c2_const_smul (c2_affineParabolicPullback hab hu hSpace hClock) _

theorem leviC_affineParabolicPotential {S O : Set (Space n)}
    {l r a b ρ τ : ℝ} {c : Space n} {u : Point n → ℝ}
    (hρ : ρ ≠ 0) (hab : a < b) (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r))
    {p : Point n} (hp : p ∈ cylinder O a b) :
    leviC (fun z => affineParabolicPotential ρ c τ u (z, p.2)) p.1 =
      leviC (fun z => u (z, (affineParabolicPoint ρ c τ p).2))
        (affineParabolicPoint ρ c τ p).1 := by
  have hNew := (c2_affineParabolicPotential hab hu hSpace hClock).2.2.2.2.1 p hp
  have hOld := hu.2.2.2.2.1 (affineParabolicPoint ρ c τ p) ⟨hSpace hp.1, hClock hp.2⟩
  rw [← leviSecondMatrixCLM_eq_native hNew, ← leviSecondMatrixCLM_eq_native hOld]
  change leviSecondMatrixCLM (spatialDD (affineParabolicPotential ρ c τ u) p) =
    leviSecondMatrixCLM (spatialDD u (affineParabolicPoint ρ c τ p))
  rw [spatialDD_affineParabolicPotential hρ]

theorem chartPotentialMatrix_affineParabolicPotential {S O : Set (Space n)}
    {l r a b ρ τ : ℝ} {c : Space n} {u : Point n → ℝ}
    (H : Point n → Matrix (Fin n) (Fin n) ℂ)
    (hρ : ρ ≠ 0) (hab : a < b) (hu : C2 (cylinder S l r) u)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r))
    {p : Point n} (hp : p ∈ cylinder O a b) :
    chartPotentialMatrix (fun q => H (affineParabolicPoint ρ c τ q))
      (affineParabolicPotential ρ c τ u) p =
      chartPotentialMatrix H u (affineParabolicPoint ρ c τ p) := by
  unfold chartPotentialMatrix
  rw [leviC_affineParabolicPotential hρ hab hu hSpace hClock hp]

theorem schauderBound_affineParabolicPotential {S O : Set (Space n)}
    {l r a b ρ τ β C : ℝ} {c : Space n} {u : Point n → ℝ}
    (hab : a < b) (hρ : |ρ| ≤ 1) (hβ : 0 ≤ β)
    (hSpace : MapsTo (fun x => ρ • x + c) O S)
    (hClock : MapsTo (fun t => τ + ρ ^ 2 * t) (Icc a b) (Icc l r))
    (hu : SchauderBound β (cylinder S l r) u C) :
    SchauderBound β (cylinder O a b) (affineParabolicPotential ρ c τ u) (|(ρ ^ 2)⁻¹| * C) :=
  schauderBound_real_mul (schauderBound_affineParabolicPullback hab hρ hβ hSpace hClock hu) _

end Yau.NodeProofs.F01Aux
