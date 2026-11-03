import Yau.Blueprint.HodgeContracts
import Yau.Blueprint.Stages

/-! The rough-potential clause of preliminaries.tex:249–267.
The upper Hessian is a distribution inequality in actual induced charts;
the heat equation and continuous initial trace are separate from its output. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
noncomputable section
namespace Yau.Blueprint
open Yau
variable {n : ℕ} {M : ComplexManifold n}

def leviDirection (H : Matrix (Fin n) (Fin n) ℂ) (v : ComplexVector n) : ℝ :=
  (star (WithLp.ofLp v) ⬝ᵥ (H *ᵥ WithLp.ofLp v)).re

def WeakLeviUpper (g : HermitianField M) (f : M.Carrier → ℝ) (C : ℝ) : Prop :=
  ∀ (x : M.Carrier) (v : ComplexVector n) (φ : ComplexVector n → ℝ),
    ContDiff ℝ ∞ φ → HasCompactSupport φ →
    closure {z | φ z ≠ 0} ⊆ chartTarget x → (∀ z, 0 ≤ φ z) →
    Integrable (fun z => inChart x f z * leviDirection (leviC φ z) v) (lebesgueC n) ∧
    Integrable (fun z => φ z * leviDirection (hMat g x z) v) (lebesgueC n) ∧
    (∫ z, inChart x f z * leviDirection (leviC φ z) v ∂lebesgueC n) ≤
      C * ∫ z, φ z * leviDirection (hMat g x z) v ∂lebesgueC n

def LipschitzForMetric (g : HermitianField M) (f : M.Carrier → ℝ) : Prop :=
  ∃ L : ℝ, 0 ≤ L ∧ ∀ x y, |f x - f y| ≤ L * lengthDist g x y

def ConstantOutsideCompact (f : M.Carrier → ℝ) : Prop :=
  ∃ (K : Set M.Carrier) (c : ℝ), IsCompact K ∧ ∀ x, x ∉ K → f x = c

/-- Bounded scalar heat on positive times with a continuous (not C∞) initial
trace. The Hessian estimate is not included in this solution class. -/
def IsContinuousInitialScalarHeat (g : HermitianField M) (f : M.Carrier → ℝ)
    (u : ℝ → M.Carrier → ℝ) : Prop :=
  (∀ x, u 0 x = f x) ∧
  SmoothSpaceTime (fun x t => u t x) (Set.Ioi 0) ∧
  (∀ x t, 0 < t → HasDerivAt (fun s => u s x)
    (laplacian g (u t) x) t) ∧
  (∀ T, 0 < T → ∃ B : ℝ, 0 ≤ B ∧ ∀ x t, 0 < t → t ≤ T → |u t x| ≤ B) ∧
  (∀ K : Set M.Carrier, IsCompact K → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ t, 0 < t → t < δ → ∀ x ∈ K, |u t x - f x| ≤ ε)

/-- Existence/uniqueness and the actual distribution-to-smooth Hessian bound.
All data are computed from the fixed initial complete metric. -/
def LipschitzHessianHeatTarget (X : KahlerManifold n) : Prop :=
  ∀ (f : Pt X → ℝ) (C : ℝ), LipschitzForMetric X.metric.form f →
    ConstantOutsideCompact f → WeakLeviUpper X.metric.form f C →
    (∃ u, IsContinuousInitialScalarHeat X.metric.form f u) ∧
    (∀ u v, IsContinuousInitialScalarHeat X.metric.form f u →
      IsContinuousInitialScalarHeat X.metric.form f v → ∀ t, 0 < t → u t = v t) ∧
    (∀ u, IsContinuousInitialScalarHeat X.metric.form f u →
      ∀ t, 0 < t → ∀ x,
        HermLE (levi (u t) x) ((C : ℂ) • gMat X.metric.form x))

end Yau.Blueprint
