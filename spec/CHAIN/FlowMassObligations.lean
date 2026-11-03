import Yau.Blueprint.Analytic
/-! Internal planning obligations registered as WP03-F04-VOLUME-ADJOINT.
These concrete predicates and the closed target are unproved. This module is
included in the default statement build; compiling it supplies no volume,
adjoint, mass inequality or scalar comparison theorem. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder NNReal
open MeasureTheory Filter
set_option autoImplicit false
noncomputable section
namespace Yau.Blueprint.FlowMass
open Yau
variable {n : ℕ}

-- In namespace Yau.Blueprint, with open Yau MeasureTheory.
def flowMassDensity {X : KahlerManifold n} (ρ : STF X) : STF X :=
  fun x t => Real.exp (-ρ x t)

def MassVolumeTransport (X : KahlerManifold n) (h : Flow X)
    (P ρ : STF X) : Prop :=
  ∀ T : ℝ, 0 < T →
    SmoothSpaceTime (flowMassDensity ρ) (Set.Icc 0 T) ∧
    (∀ x t, t ∈ Set.Icc 0 T →
      0 < flowMassDensity ρ x t ∧ flowMassDensity ρ x t ≤ 1 ∧
      flowMassDensity ρ x t = Real.exp (P x t) ∧
      flowMassDensity ρ x t =
        (gMat (h t) x).det.re / (gMat X.metric.form x).det.re ∧
      HasDerivWithinAt (flowMassDensity ρ x)
        (-scalarCurvature (h t) x * flowMassDensity ρ x t)
        (Set.Icc 0 T) t) ∧
    (∀ μg : Measure (Pt X), IsRiemannianVolume X.metric.form μg →
      ∀ t ∈ Set.Icc 0 T, ∀ μt : Measure (Pt X), IsRiemannianVolume (h t) μt →
        μt = μg.withDensity (fun x => ENNReal.ofReal (flowMassDensity ρ x t)))

def RiemannianVolumeLocality (X : KahlerManifold n) : Prop :=
  ∀ μ : Measure (Pt X), IsRiemannianVolume X.metric.form μ →
    (∀ K : Set (Pt X), IsCompact K → μ K < ⊤) ∧
    (∀ O : Set (Pt X), IsOpen O → O.Nonempty → 0 < μ O)

def CompactKahlerAdjoint (X : KahlerManifold n) (h : Flow X) : Prop :=
  ∀ t : ℝ, 0 ≤ t → ∀ μt : Measure (Pt X), IsRiemannianVolume (h t) μt →
    ∀ v ψ : Pt X → ℝ, SmoothFn v → SmoothFn ψ → HasCompactSupport ψ →
      (∫ x, ψ x * laplacian (h t) v x ∂μt) =
        ∫ x, v x * laplacian (h t) ψ x ∂μt

/-- Closed internal target. No theorem or assumption is supplied by this definition.
Proof route: actual G02 volumes, G04 density normalization, determinant
calculus and compact Kähler adjoint. No F04 conclusion occurs as a premise. -/
def VolumeAdjointTarget : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ →
    MassVolumeTransport X h P ρ ∧
      RiemannianVolumeLocality X ∧ CompactKahlerAdjoint X h

end Yau.Blueprint.FlowMass
