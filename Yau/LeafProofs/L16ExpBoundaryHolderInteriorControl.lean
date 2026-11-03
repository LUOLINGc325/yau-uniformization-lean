import Yau.LeafProofs.L16ExpBoundaryHolderCoefficients
import Yau.LeafProofs.L16DeGiorgiOscillationIteration

open Filter Set
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

noncomputable section

namespace Yau.LeafProofs.L16ExpBoundaryHolderAux

open Yau.Parabolic L16Aux

/-- The precise interior oscillation statement, with all actual differential
fields and coefficient bounds. It is separate from the global target. -/
def InteriorOscillationEstimate (n : ℕ) (ν L γ C : ℝ) : Prop :=
  ∀ D F : ℝ, 0 ≤ D → 0 ≤ F → ∀ (p₀ : Point n) (R : ℝ), 0 < R → R ≤ dgOscDriftRadius D →
    ∀ (A : Point n → Mat n) (c : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ),
    DGClassicalFields (dgOscCylinderOpen p₀ R) A c f u →
    ClassicalDivEq (dgOscCylinderOpen p₀ R) A c f u →
    DGUniformBounds (dgOscCylinderOpen p₀ R) A c f ν L D F →
    ContinuousOn u (dgOscCylinder p₀ R) →
    ∀ ell width : ℝ, 0 ≤ width → (∀ p ∈ dgOscCylinder p₀ R, ell ≤ u p ∧ u p ≤ ell+width) →
    ∀ r : ℝ, 0 < r → r ≤ R → ∀ p ∈ dgOscCylinder p₀ r, ∀ q ∈ dgOscCylinder p₀ r,
      |u p-u q| ≤ C*(r/R)^γ*(width+F*R^2)

/-- Only interior cylinders contained in the equation region are queried by
the global gluing argument. The outer interval is supplied explicitly. -/
def LocalOscillationControl {n : ℕ} (O : Set (Space n)) (T γ C F ρ : ℝ)
    (u : Point n → ℝ) : Prop :=
  ∀ (p₀ : Point n) (R : ℝ), 0 < R → R ≤ ρ →
    dgOscCylinderOpen p₀ R ⊆ O ×ˢ Ioo 0 T →
    dgOscCylinder p₀ R ⊆ cylinder (closure O) 0 T →
    ∀ ell width : ℝ, 0 ≤ width → (∀ p ∈ dgOscCylinder p₀ R, ell ≤ u p ∧ u p ≤ ell+width) →
    ∀ r : ℝ, 0 < r → r ≤ R → ∀ p ∈ dgOscCylinder p₀ r, ∀ q ∈ dgOscCylinder p₀ r,
      |u p-u q| ≤ C*(r/R)^γ*(width+F*R^2)

theorem localOscillationControl_of_DG {n : ℕ} {O : Set (Space n)} {T ν L γ C D F ρ : ℝ}
    (hCore : InteriorOscillationEstimate n ν L γ C) (hD : 0 ≤ D) (hF : 0 ≤ F)
    (hρ : ρ ≤ dgOscDriftRadius D)
    {A : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {f u : Point n → ℝ}
    (hfields : DGClassicalFields (O ×ˢ Ioo 0 T) A c f u)
    (hpde : ClassicalDivEq (O ×ˢ Ioo 0 T) A c f u)
    (hBounds : DGUniformBounds (O ×ˢ Ioo 0 T) A c f ν L D F)
    (hu : ContinuousOn u (cylinder (closure O) 0 T)) :
    LocalOscillationControl O T γ C F ρ u := by
  intro p₀ R hR hRρ hOpen hClosed ell width hWidth hRange r hr hrR p hp q hq
  exact hCore D F hD hF p₀ R hR (hRρ.trans hρ) A c f u
    (dgOsc_fields_mono hOpen hfields) (fun z hz => hpde z (hOpen hz))
    (dgOsc_uniform_restrict hOpen hBounds) (hu.mono hClosed)
    ell width hWidth hRange r hr hrR p hp q hq

/-- The actual proved De Giorgi core discharges the independent analytic
statement; no new hypothesis will remain in the final leaf theorem. -/
theorem exists_interiorOscillationEstimate {n : ℕ} (hn : 0 < n) {ν L : ℝ}
    (hν : 0 < ν) (hνL : ν ≤ L) :
    ∃ γ C : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < C ∧ InteriorOscillationEstimate n ν L γ C :=
  dgOsc_interior_oscillation hn hν hνL

end Yau.LeafProofs.L16ExpBoundaryHolderAux
