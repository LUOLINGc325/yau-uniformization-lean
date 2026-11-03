import Yau.Geometry.Calculus

/-!
Local Chern calculus and the maximal distributional Dolbeault graph on actual
coefficient bundles. Fibres and trivializations are Mathlib vector bundles;
there is no global frame or embedding assumption. The forms below are intrinsic
mixed alternating tensors, with complex linear top slots and conjugate linear
antiholomorphic slots. This file states no analytic existence theorem.
-/

open scoped Manifold Topology ContDiff ComplexOrder ENNReal Matrix
open MeasureTheory Bundle

noncomputable section
namespace Yau
namespace BundleDbar

variable {n r : ℕ} {M : ComplexManifold n}

/-- The three coefficient fibres in preliminaries:98–110 are actual linear
algebra constructions. Their bundle topologies and holomorphic atlas instances
are not asserted here; constructing those instances is a remaining bridge. -/
abbrev CanonicalFiber (M : ComplexManifold n) (x : M.Carrier) :=
  (TangentVector M x) [⋀^Fin n]→L[ℂ] ℂ

abbrev AntiCanonicalFiber (M : ComplexManifold n) (x : M.Carrier) :=
  CanonicalFiber M x →L[ℂ] ℂ

abbrev TrivialLineFiber (M : ComplexManifold n) (_x : M.Carrier) := ComplexVector 1

abbrev TangentAntiCanonicalFiber (M : ComplexManifold n) (x : M.Carrier) :=
  TensorProduct ℂ (TangentVector M x) (AntiCanonicalFiber M x)

/-- Anticanonical induced metric, in the frame dual to `dz₁ ∧ ... ∧ dzₙ`. -/
def antiCanonicalMetricMatrix (g : HermitianField M) (a : M.Carrier)
    (z : ComplexVector n) : Matrix (Fin 1) (Fin 1) ℂ :=
  fun _ _ => (hMat g a z).det

def trivialLineMetricMatrix (_z : ComplexVector n) : Matrix (Fin 1) (Fin 1) ℂ := 1

/-- Tangent times anticanonical metric, with no Nakano assumption on tangent. -/
def tangentAntiCanonicalMetricMatrix (g : HermitianField M) (a : M.Carrier)
    (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  (hMat g a z).det • hMat g a z

variable (E : M.Carrier → Type) [∀ x, NormedAddCommGroup (E x)]
  [∀ x, NormedSpace ℂ (E x)] [∀ x, NormedSpace ℝ (E x)]
  [∀ x, IsScalarTower ℝ ℂ (E x)]
  [TopologicalSpace (TotalSpace (ComplexVector r) E)]
  [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E]

/-- Holomorphicity constrains the actual linear transition maps on every atlas
overlap. The `ℂ` model makes `ContMDiff` complex differentiability. -/
def Holomorphic : Prop := ContMDiffVectorBundle ⊤ (ComplexVector r) E (ComplexModel n)

abbrev Metric := ∀ x, HermitianInnerProduct (E x)

abbrev localTriv (a : M.Carrier) := trivializationAt (ComplexVector r) E a

/-- Common domain of the manifold chart and the bundle trivialization. -/
def localDomain (a : M.Carrier) : Set (ComplexVector n) :=
  chartTarget a ∩ (chartInv a) ⁻¹' (localTriv (r := r) E a).baseSet

/-- Gram matrix in a genuine local holomorphic bundle frame. -/
def metricMatrix (h : Metric E) (a : M.Carrier) (z : ComplexVector n) :
    Matrix (Fin r) (Fin r) ℂ :=
  fun α β => (h (chartInv a z)).toFun
    ((localTriv (r := r) E a).symmL ℂ (chartInv a z) (stdVec α))
    ((localTriv (r := r) E a).symmL ℂ (chartInv a z) (stdVec β))

def SmoothMetric (h : Metric E) : Prop :=
  ∀ a α β, ContDiffOn ℝ ∞ (fun z => metricMatrix (r := r) E h a z α β) (localDomain (r := r) E a)

/-- `H⁻¹ ∂H` in column coordinates, for `h(u,v)=u* H v`. -/
def chernConnectionMatrix (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (i : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  (H z)⁻¹ * (Matrix.of fun α β => wirt (fun w => H w α β) z (stdVec i))

/-- Metric-lowered Chern curvature: `-H ∂̄(H⁻¹ ∂H)`.
Thus a line metric `exp(-φ)` has curvature `∂∂̄φ`. -/
def curvatureMatrix (H : ComplexVector n → Matrix (Fin r) (Fin r) ℂ)
    (z : ComplexVector n) (i j : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  -(H z * (Matrix.of fun α β => wirtBar
    (fun w => chernConnectionMatrix H w i α β) z (stdVec j)))

def curvature (h : Metric E) (a : M.Carrier) (z : ComplexVector n)
    (i j : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  curvatureMatrix (metricMatrix (r := r) E h a) z i j

def griffithsQuadratic
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (ξ : ComplexVector n) (v : ComplexVector r) : ℝ :=
  (∑ i, ∑ j, ∑ α : Fin r, ∑ β : Fin r,
    R i j α β * ξ i * star (ξ j) * star (v α) * v β).re

def nakanoQuadratic
    (R : Fin n → Fin n → Matrix (Fin r) (Fin r) ℂ)
    (U : Fin n → Fin r → ℂ) : ℝ :=
  (∑ i, ∑ j, ∑ α : Fin r, ∑ β : Fin r, R i j α β * star (U j α) * U i β).re

def GriffithsNonnegative (h : Metric E) : Prop :=
  ∀ a z, z ∈ localDomain (r := r) E a → ∀ ξ v,
    0 ≤ griffithsQuadratic (curvature (r := r) E h a z) ξ v

def NakanoNonnegative (h : Metric E) : Prop :=
  ∀ a z, z ∈ localDomain (r := r) E a → ∀ U,
    0 ≤ nakanoQuadratic (curvature (r := r) E h a z) U

/-- Actual tensor determinant fibre `E ⊗ Λ^r E`, realised by the dual of the
top alternating forms on `E*`. No global holomorphic frame is chosen. -/
abbrev TensorDetFiber (x : M.Carrier) :=
  TensorProduct ℂ (E x) ((E x →ₗ[ℂ] ℂ) [⋀^Fin r]→ₗ[ℂ] ℂ)

def dualFrame (a x : M.Carrier) (i : Fin r) : E x →ₗ[ℂ] ℂ where
  toFun v := (localTriv (r := r) E a).continuousLinearMapAt ℂ x v i
  map_add' v w := by simp
  map_smul' c v := by simp

/-- Coordinates of the actual tensor determinant fibre. For a pure tensor
`v ⊗ d` they are `d(e¹,...,eʳ) · e(v)`. -/
def tensorDetCoordinates (a x : M.Carrier) : TensorDetFiber (r := r) E x →ₗ[ℂ] ComplexVector r :=
  TensorProduct.lift
    { toFun := fun v =>
        { toFun := fun d => d (dualFrame (r := r) E a x) •
            (localTriv (r := r) E a).continuousLinearMapAt ℂ x v
          map_add' := by intros; simp [add_smul]
          map_smul' := by intros; simp [smul_smul] }
      map_add' := by intros; ext; simp [smul_add]
      map_smul' := by intros; ext; simp [smul_smul, mul_comm] }

/-- Induced metric in the local tensor frame `e_α ⊗ (e₁ ∧ ... ∧ e_r)`. -/
def tensorDetMetricMatrix (h : Metric E) (a : M.Carrier) (z : ComplexVector n) :
    Matrix (Fin r) (Fin r) ℂ :=
  (metricMatrix (r := r) E h a z).det • metricMatrix (r := r) E h a z

/-- The induced local pairing on the actual tensor fibre, from the computed
coordinates above. Descent of these local expressions is not assumed. -/
def tensorDetLocalPairing (h : Metric E) (a x : M.Carrier)
    (u v : TensorDetFiber (r := r) E x) : ℂ :=
  ∑ α, ∑ β, star (tensorDetCoordinates (r := r) E a x u α) *
    tensorDetMetricMatrix (r := r) E h a (chartPt a x) α β *
      tensorDetCoordinates (r := r) E a x v β

/-- Nakano nonnegativity of the tensor determinant metric, computed directly
from its induced local metric. This is the conclusion of the internal
Demailly–Skoda target, not an assumed curvature field. -/
def TensorDetNakanoNonnegative (h : Metric E) : Prop :=
  ∀ a z, z ∈ localDomain (r := r) E a → ∀ U,
    0 ≤ nakanoQuadratic (curvatureMatrix (tensorDetMetricMatrix (r := r) E h a) z) U

/-- Holomorphic top slots and real alternating antiholomorphic slots. -/
abbrev MixedTensor (x : M.Carrier) (q : ℕ) :=
  (TangentVector M x) [⋀^Fin q]→ₗ[ℝ]
    ((TangentVector M x) [⋀^Fin n]→ₗ[ℂ] E x)

def AntiComplexLinear {x : M.Carrier} {q : ℕ} (A : MixedTensor E x q) : Prop :=
  ∀ (v : Fin q → TangentVector M x) (i : Fin q) (c : ℂ),
    A (Function.update v i (c • v i)) = star c • A v

/-- Actual E-valued `(n,q)` tensors on M. -/
abbrev NQForm (q : ℕ) := ∀ x : M.Carrier,
  {A : MixedTensor E x q // AntiComplexLinear E A}

/-- Local coefficients obtained by evaluation of the intrinsic form and the
actual linear bundle trivialization, rather than supplied as independent data.
The convention is `dbar z_I ∧ dz_1 ∧ ... ∧ dz_n`. -/
def coefficients {q : ℕ} (u : NQForm E q) (a : M.Carrier)
    (z : ComplexVector n) (I : Fin q → Fin n) : ComplexVector r :=
  (localTriv (r := r) E a).continuousLinearMapAt ℂ (chartInv a z)
    (((u (chartInv a z)).1
      (fun k => chartVec a (chartInv a z) (stdVec (I k))))
      (fun k => chartVec a (chartInv a z) (stdVec k)))

def SmoothForm {q : ℕ} (u : NQForm E q) : Prop :=
  ∀ a I α, ContDiffOn ℝ ∞ (fun z => coefficients (r := r) E u a z I α) (localDomain (r := r) E a)

/-- Local alternating Dolbeault derivative, in a holomorphic frame. -/
def dbarCoefficients {q : ℕ} (u : NQForm E q) (a : M.Carrier)
    (z : ComplexVector n) (I : Fin (q + 1) → Fin n) (α : Fin r) : ℂ :=
  ∑ k : Fin (q + 1), (-1 : ℂ) ^ k.val *
    wirtBar (fun w => coefficients (r := r) E u a w (fun l => I (k.succAbove l)) α)
      z (stdVec (I k))

/-- Local square integrability, with an explicit measurability requirement.
No integral is allowed to stand for a nonintegrable distribution coefficient. -/
def LocallyL2 {q : ℕ} (u : NQForm E q) : Prop :=
  ∀ a I α,
    AEStronglyMeasurable (fun z => coefficients (r := r) E u a z I α)
      ((lebesgueC n).restrict (localDomain (r := r) E a)) ∧
    ∀ K : Set (ComplexVector n), IsCompact K → K ⊆ localDomain (r := r) E a →
      (∫⁻ z in K, ENNReal.ofReal (‖coefficients (r := r) E u a z I α‖ ^ 2)
        ∂lebesgueC n) < ⊤

/-- Distributional `dbar u=f`, tested against every compactly supported smooth
scalar test function in every chart/frame domain. Nonconjugated distribution
testing accounts for the minus sign in integration by parts. -/
def WeakDbar {q : ℕ} (u : NQForm E q) (f : NQForm E (q + 1)) : Prop :=
  LocallyL2 (r := r) E u ∧ LocallyL2 (r := r) E f ∧
  ∀ a (I : Fin (q + 1) → Fin n) α (ψ : ComplexVector n → ℂ),
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ localDomain (r := r) E a →
    (∫ z, coefficients (r := r) E f a z I α * ψ z ∂lebesgueC n) =
      -∑ k : Fin (q + 1), (-1 : ℂ) ^ k.val *
        ∫ z, coefficients (r := r) E u a z (fun l => I (k.succAbove l)) α *
          wirtBar ψ z (stdVec (I k)) ∂lebesgueC n

def WeaklyClosed {q : ℕ} (f : NQForm E q) : Prop :=
  LocallyL2 (r := r) E f ∧
  ∀ a (I : Fin (q + 1) → Fin n) α (ψ : ComplexVector n → ℂ),
    ContDiff ℝ ∞ ψ → HasCompactSupport ψ → tsupport ψ ⊆ localDomain (r := r) E a →
    (∑ k : Fin (q + 1), (-1 : ℂ) ^ k.val *
      ∫ z, coefficients (r := r) E f a z (fun l => I (k.succAbove l)) α *
        wirtBar ψ z (stdVec (I k)) ∂lebesgueC n) = 0

/-- Standard exterior tensor norm, with `1/q!` for all ordered anti-indices
and determinant of the cotangent metric for the top holomorphic slots. -/
def formNormSq {q : ℕ} (g : HermitianField M) (h : Metric E)
    (u : NQForm E q) (x : M.Carrier) : ℝ :=
  (Nat.factorial q : ℝ)⁻¹ * (gMat g x)⁻¹.det.re *
    (∑ I : Fin q → Fin n, ∑ J : Fin q → Fin n, ∑ α : Fin r, ∑ β : Fin r,
      star (coefficients (r := r) E u x (chartPt x x) I α) * metricMatrix (r := r) E h x (chartPt x x) α β *
      coefficients (r := r) E u x (chartPt x x) J β * ∏ k, (gMat g x)⁻¹ (I k) (J k)).re

def weightedNormSq {q : ℕ} (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (u : NQForm E q) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (formNormSq (r := r) E g h u x * Real.exp (-φ x)) ∂μ

def WeightedL2 {q : ℕ} (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (u : NQForm E q) : Prop :=
  LocallyL2 (r := r) E u ∧ weightedNormSq (r := r) E g h μ φ u < ⊤

/-- The maximal weighted distributional graph, before quotienting by a.e.
equality. Its AE quotient and graph closedness remain separate obligations. -/
def MaximalDbarGraph {q : ℕ} (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ)
    (u : NQForm E q) (f : NQForm E (q + 1)) : Prop :=
  WeightedL2 (r := r) E g h μ φ u ∧ WeightedL2 (r := r) E g h μ φ f ∧ WeakDbar (r := r) E u f

/-- The actual a.e. quotient relation on the weighted finite-norm sections. -/
def weightedL2Setoid {q : ℕ} (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) :
    Setoid {u : NQForm E q // WeightedL2 (r := r) E g h μ φ u} where
  r u v := ∀ᵐ x ∂μ, u.1 x = v.1 x
  iseqv :=
    ⟨fun _ => Filter.Eventually.of_forall (fun _ => rfl),
      fun h => h.mono (fun _ hx => hx.symm),
      fun h k => (h.and k).mono (fun _ hx => hx.1.trans hx.2)⟩

/-- Weighted L² forms as genuine a.e. equivalence classes. The Hilbert
structure and closedness of the maximal graph have not been proved. -/
abbrev WeightedL2Space (q : ℕ) (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) :=
  Quotient (weightedL2Setoid (r := r) (q := q) E g h μ φ)

/-- Maximal Dolbeault relation on actual weighted L² classes. The existential
representative formulation saturates the concrete distributional graph by a.e.
equality, without silently assuming its unproved well-definedness/closedness
or a freely chosen unbounded operator. -/
def MaximalDbarL2Graph {q : ℕ} (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ)
    (u : WeightedL2Space (r := r) E q g h μ φ)
    (f : WeightedL2Space (r := r) E (q + 1) g h μ φ) : Prop :=
  ∃ (u₀ : {u : NQForm E q // WeightedL2 (r := r) E g h μ φ u})
    (f₀ : {f : NQForm E (q + 1) // WeightedL2 (r := r) E g h μ φ f}),
    Quotient.mk _ u₀ = u ∧ Quotient.mk _ f₀ = f ∧ WeakDbar (r := r) E u₀.1 f₀.1

/-- Weighted curvature `R_h + ∂∂̄φ ⊗ h`, with the derivative-index transpose
needed by `leviC a b = ∂_b ∂̄_a`. -/
def weightedCurvature (h : Metric E) (φ : M.Carrier → ℝ)
    (a : M.Carrier) (z : ComplexVector n) (i j : Fin n) : Matrix (Fin r) (Fin r) ℂ :=
  curvature (r := r) E h a z i j + (leviC (inChart a φ) z j i) • metricMatrix (r := r) E h a z

def WeightedNakanoNonnegative (h : Metric E) (φ : M.Carrier → ℝ) : Prop :=
  ∀ a z, z ∈ localDomain (r := r) E a → ∀ U,
    0 ≤ nakanoQuadratic (weightedCurvature (r := r) E h φ a z) U

/-- Pairing on `(n,1)` coefficients. -/
def coefficientInner (g : HermitianField M) (h : Metric E) (x : M.Carrier)
    (F V : Fin n → Fin r → ℂ) : ℂ :=
  (gMat g x)⁻¹.det * ∑ i, ∑ j, ∑ α : Fin r, ∑ β : Fin r,
    star (F i α) * metricMatrix (r := r) E h x (chartPt x x) α β * (gMat g x)⁻¹ i j * V j β

/-- The curvature operator `[iΘ,Λ]` quadratic form on `(n,1)` coefficients;
both covector slots are raised with the actual base metric. -/
def curvatureEnergy (g : HermitianField M) (h : Metric E) (φ : M.Carrier → ℝ)
    (x : M.Carrier) (V : Fin n → Fin r → ℂ) : ℝ :=
  (gMat g x)⁻¹.det.re * nakanoQuadratic
    (weightedCurvature (r := r) E h φ x (chartPt x x))
    (fun i α => ∑ j, (gMat g x)⁻¹ i j * V j α)

/-- Variational inverse-curvature norm. For positive B this is
`<B⁻¹f,f>`; for semipositive B it is the extended inverse norm (possibly ∞).
This avoids the invalid convention that the inverse of a singular matrix
vanishes. -/
def inverseCurvatureNormSq (g : HermitianField M) (h : Metric E)
    (φ : M.Carrier → ℝ) (f : NQForm E 1) (x : M.Carrier) : ℝ≥0∞ :=
  ⨆ V : Fin n → Fin r → ℂ, ENNReal.ofReal
    (2 * (coefficientInner (r := r) E g h x
      (fun i α => coefficients (r := r) E f x (chartPt x x) (fun _ => i) α) V).re -
      curvatureEnergy (r := r) E g h φ x V)

def inverseCurvatureIntegral (g : HermitianField M) (h : Metric E)
    (μ : Measure M.Carrier) (φ : M.Carrier → ℝ) (f : NQForm E 1) : ℝ≥0∞ :=
  ∫⁻ x, inverseCurvatureNormSq (r := r) E g h φ f x * ENNReal.ofReal (Real.exp (-φ x)) ∂μ

/-- Actual tensor subtraction; no section quotient is identified
with its representatives. -/
def subForm {q : ℕ} (u v : NQForm E q) : NQForm E q := fun x =>
  ⟨(u x).1 - (v x).1, by
    intro w i c
    change (u x).1 (Function.update w i (c • w i)) -
        (v x).1 (Function.update w i (c • w i)) =
      star c • ((u x).1 w - (v x).1 w)
    rw [(u x).2 w i c, (v x).2 w i c, smul_sub]⟩

/-- Coefficient holomorphicity of the actual top form in every genuine
chart/frame domain. This is a definition, not a regularity theorem. -/
def HolomorphicTopForm (u : NQForm E 0) : Prop :=
  ∀ a α, DifferentiableOn ℂ
    (fun z => coefficients (r := r) E u a z Fin.elim0 α)
    (localDomain (r := r) E a)

/-- The computed derivative relation. Existence of a globally glued f with
this relation, smoothness and weak closedness is still an internal obligation. -/
def IsDbarOf (u : NQForm E 0) (f : NQForm E 1) : Prop :=
  ∀ a z, z ∈ localDomain (r := r) E a → ∀ I α,
    coefficients (r := r) E f a z I α =
      dbarCoefficients (r := r) E u a z I α


end BundleDbar
end Yau
