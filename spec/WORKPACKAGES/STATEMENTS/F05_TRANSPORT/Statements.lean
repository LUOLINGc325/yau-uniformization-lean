import spec.CHAIN.HeatConcreteBindings
import spec.CHAIN.ParabolicCandidates

/-! Statement proposals only. An atlas is an existence OUTPUT of the actual
smooth-domain predicate, never an additional hypothesis of F05. No analytic
assertion is proved here. All coordinates, norms and operators are computed. -/
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
noncomputable section
namespace Yau.F05Transport
open Yau.Parabolic Yau.ParabolicCandidates Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

/-- Data only: the geometric constraints are a separate predicate. None of
these fields can carry a proposition or a desired analytic estimate. -/
structure AtlasData (M : ComplexManifold n) where
  count : ℕ
  center : Fin count → M.Carrier
  forward : Fin count → Space n → Space n
  inverse : Fin count → Space n → Space n
  normal : Fin count → Option (RIdx n)

/-- The source is computed from the actual chart target and flattening map. -/
def AtlasData.source (A : AtlasData M) (i : Fin A.count) : Set (Space n) :=
  chartTarget (A.center i) ∩ A.forward i ⁻¹' Metric.ball 0 3

def region (ν : Option (RIdx n)) (r : ℝ) : Set (Space n) :=
  {z | ‖z‖ ≤ r ∧ match ν with | none => True | some i => realCoord z i ≤ 0}

def lift (A : AtlasData M) (i : Fin A.count) (z : Space n) : M.Carrier :=
  chartInv (A.center i) (A.inverse i z)

def pull (A : AtlasData M) (i : Fin A.count)
    (u : M.Carrier → ℝ → ℝ) (p : Point n) : ℝ := u (lift A i p.1) p.2

def rawPull (x : M.Carrier) (u : M.Carrier → ℝ → ℝ) (p : Point n) : ℝ :=
  u (chartInv x p.1) p.2

/-- Buffered diffeomorphisms in actual manifold charts. The only flattened
boundary is the genuine frontier of O; the radius-two rim has no trace data.
All-order control concerns the actual maps, and is not an estimate witness. -/
def GenuineAtlas (O : Set M.Carrier) (A : AtlasData M) : Prop :=
  (∀ i, IsOpen (A.source i) ∧ A.source i ⊆ chartTarget (A.center i) ∧
    ContDiffOn ℝ ∞ (A.forward i) (A.source i) ∧
    ContDiffOn ℝ ∞ (A.inverse i) (Metric.ball 0 3) ∧
    A.inverse i '' Metric.ball 0 3 ⊆ A.source i ∧
    (∀ z ∈ Metric.ball 0 3, A.forward i (A.inverse i z) = z) ∧
    (∀ z ∈ A.source i, A.inverse i (A.forward i z) = z) ∧
    (∀ z ∈ Metric.ball 0 3,
      (lift A i z ∈ O ↔ match A.normal i with
        | none => True | some a => realCoord z a < 0) ∧
      (lift A i z ∈ closure O ↔ match A.normal i with
        | none => True | some a => realCoord z a ≤ 0) ∧
      (lift A i z ∈ frontier O ↔ match A.normal i with
        | none => False | some a => realCoord z a = 0))) ∧
  closure O ⊆ ⋃ i, lift A i '' region (A.normal i) 1 ∧
  ∀ k : ℕ, ∃ C : ℝ, 0 < C ∧ ∀ i, ∀ z ∈ Metric.closedBall 0 2,
    ‖iteratedFDeriv ℝ k (A.inverse i) z‖ ≤ C ∧
    ‖iteratedFDeriv ℝ k (A.forward i) (A.inverse i z)‖ ≤ C

def FiniteAtlasTarget : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (M : ComplexManifold n) (O : Set M.Carrier),
    SmoothPrecompactDomain O → ∃ A : AtlasData M, GenuineAtlas O A

/-- The principal coefficient is computed by polarization of the SAME
complex trace/Levi operator, fixing its normalization without a free matrix. -/
def baseA (h : HermitianField M) (x : M.Carrier) (z : Space n) : Mat n :=
  fun i j => (1/2 : ℝ) * traceWith (hMat h x z)
    (leviC (fun w => realCoord w i * realCoord w j) z)

def flatA (h : HermitianField M) (A : AtlasData M) (i : Fin A.count)
    (p : Point n) : Mat n :=
  fun a b => ∑ c, ∑ e, baseA h (A.center i) (A.inverse i p.1) c e *
    d (fun w => realCoord (A.forward i w) a) (A.inverse i p.1) c *
    d (fun w => realCoord (A.forward i w) b) (A.inverse i p.1) e

def flatB (h : HermitianField M) (A : AtlasData M) (i : Fin A.count)
    (p : Point n) (a : RIdx n) : ℝ :=
  traceWith (hMat h (A.center i) (A.inverse i p.1))
    (leviC (fun w => realCoord (A.forward i w) a) (A.inverse i p.1))

def flatR (h : HermitianField M) (A : AtlasData M) (i : Fin A.count)
    (p : Point n) : ℝ := scalarCurvature h (lift A i p.1)

/-- Both the coordinate equation and ellipticity are OUTPUTS. Neither an
operator nor coefficient/density normalization is supplied by the caller. -/
def CoordinateLaplacianTarget : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (M : ComplexManifold n) (O : Set M.Carrier)
    (h : HermitianField M), MetricSmooth h →
    (∀ x z, z ∈ chartTarget x → (hMat h x z).PosDef) →
    ∀ A : AtlasData M, GenuineAtlas O A →
    (∃ lam upper : ℝ, ∀ i,
      Elliptic (cylinder (region (A.normal i) 2) 0 1) (flatA h A i) lam upper) ∧
    (∀ i, ∀ f : M.Carrier → ℝ, SmoothFn f → ∀ z ∈ region (A.normal i) 2,
      laplacian h f (lift A i z) =
        (∑ a, ∑ b, flatA h A i (z,0) a b *
          spatialDD (pull A i (fun x _ => f x)) (z,0) (realVec a) (realVec b)) +
        ∑ a, flatB h A i (z,0) a *
          spatialD (pull A i (fun x _ => f x)) (z,0) (realVec a)) ∧
    ∀ S : ℝ, 0 < S → ∀ u : M.Carrier → ℝ → ℝ,
      (∀ i, C2 (cylinder (region (A.normal i) 2) 0 S) (pull A i u)) →
      (∀ x ∈ O, ∀ t ∈ Set.Ioc 0 S,
        derivWithin (u x) (Set.Icc 0 S) t =
          Real.exp (-u x t) * laplacian h (fun y => u y t) x +
          (1-Real.exp (-u x t))*scalarCurvature h x) →
      ∀ i, ∀ z ∈ region (A.normal i) 2, ∀ t ∈ Set.Ioc 0 S,
        (match A.normal i with | none => True | some a => realCoord z a < 0) →
        linearOp (cylinder (region (A.normal i) 2) 0 S)
          (fun p a b => Real.exp (-pull A i u p) * flatA h A i p a b)
          (fun p a => Real.exp (-pull A i u p) * flatB h A i p a)
          (pull A i u) (z,t) =
            (1-Real.exp (-pull A i u (z,t))) * flatR h A i (z,t)

/-- Existing HolderBound/SchauderBound on the actual unflattened chart image.
The predicate changes the coordinates, not the norm or differential operators. -/
def ChartHolder (A : AtlasData M) (i : Fin A.count) (r α s t : ℝ)
    (u : M.Carrier → ℝ → ℝ) (B : ℝ) : Prop :=
  HolderBound α (cylinder (A.inverse i '' region (A.normal i) r) s t)
    (rawPull (A.center i) u) B

def ChartSchauder (A : AtlasData M) (i : Fin A.count) (r α s t : ℝ)
    (u : M.Carrier → ℝ → ℝ) (B : ℝ) : Prop :=
  SchauderBound α (cylinder (A.inverse i '' region (A.normal i) r) s t)
    (rawPull (A.center i) u) B

/-- Constants depend on the fixed genuine atlas, exponent and full horizon,
before the current endpoint and functions. Both transport directions retain
all first/second spatial and one-sided temporal terms in the actual norms. -/
def NormTransportTarget : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (M : ComplexManifold n) (O : Set M.Carrier)
    (A : AtlasData M), GenuineAtlas O A → ∀ α S : ℝ,
    0 < α → α < 1 → 0 < S → ∃ C : ℝ, 0 < C ∧
    ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ S →
    ∀ (u : M.Carrier → ℝ → ℝ) (B : ℝ), 0 ≤ B → ∀ i,
      (ChartHolder A i 2 α s t u B →
        HolderBound α (cylinder (region (A.normal i) 2) s t) (pull A i u) (C*B)) ∧
      (HolderBound α (cylinder (region (A.normal i) 2) s t) (pull A i u) B →
        ChartHolder A i 2 α s t u (C*B)) ∧
      (ChartSchauder A i 2 α s t u B →
        SchauderBound α (cylinder (region (A.normal i) 2) s t) (pull A i u) (C*B)) ∧
      (SchauderBound α (cylinder (region (A.normal i) 2) s t) (pull A i u) B →
        ChartSchauder A i 2 α s t u (C*B))

/-- Within derivatives keep higher boundary jets independent of arbitrary
values outside the genuine domain. none denotes time, some a spatial a. -/
def jet (Q : Set (Point n)) : List (Option (RIdx n)) →
    (Point n → ℝ) → Point n → ℝ
  | [], v => v
  | a :: w, v => fun p => fderivWithin ℝ (jet Q w v) Q p
      (match a with | none => (0,1) | some b => (realVec b,0))

/-- Computed normal recovery quotient for u_t=e^-u Δ_h u+(1-e^-u)R.
The excluded pair is exactly the normal-normal principal term. -/
def normalRecovery (h : HermitianField M) (A : AtlasData M) (i : Fin A.count)
    (ν : RIdx n) (Q : Set (Point n)) (v : Point n → ℝ) (p : Point n) : ℝ :=
  (Real.exp (v p) * jet Q [none] v p - (Real.exp (v p)-1)*flatR h A i p -
    (∑ a, ∑ b, if a = ν ∧ b = ν then 0 else
      flatA h A i p a b * jet Q [some a, some b] v p) -
    ∑ a, flatB h A i p a * jet Q [some a] v p) / flatA h A i p ν ν

/-- Genuine initial/lateral values only, for the SAME actual u and smooth p. -/
def Dirichlet (O : Set M.Carrier) (S : ℝ) (u p : M.Carrier → ℝ → ℝ) : Prop :=
  (∀ x ∈ closure O, u x 0 = p x 0) ∧
  ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 S, u x t = p x t

/-- Positive-time higher recovery with uniform moving-endpoint constants.
The fixed smooth boundary data and base Schauder budget precede B. There is
no all-order compatibility at the original corner. All derivatives use the
strictly positive buffer δ, and there is no trace condition at a chart rim. -/
def HigherBoundaryRecoveryTarget : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (M : ComplexManifold n) (O : Set M.Carrier)
    (h : HermitianField M), SmoothPrecompactDomain O → MetricSmooth h →
    (∀ x z, z ∈ chartTarget x → (hMat h x z).PosDef) →
    ∀ (A : AtlasData M), GenuineAtlas O A → ∀ S α L : ℝ,
    0 < S → 0 < α → α < 1 → 0 < L →
    ∀ p : M.Carrier → ℝ → ℝ, SmoothSpaceTime p (Set.Icc 0 S) →
    ∀ δ : ℝ, 0 < δ → δ < S → ∀ k : ℕ,
    ∃ B : ℝ, 0 < B ∧ ∀ τ : ℝ, δ < τ → τ ≤ S →
    ∀ u : M.Carrier → ℝ → ℝ,
    Dirichlet O τ u p →
    (∀ i, SchauderBound α (cylinder (region (A.normal i) 2) 0 τ) (pull A i u) L) →
    (∀ x ∈ O, ∀ t ∈ Set.Ioc 0 τ,
      derivWithin (u x) (Set.Icc 0 τ) t =
        Real.exp (-u x t) * laplacian h (fun y => u y t) x +
        (1-Real.exp (-u x t))*scalarCurvature h x) →
      (∀ i, ContDiffOn ℝ ∞ (pull A i u)
        (cylinder (region (A.normal i) 1) δ τ)) ∧
      ∀ i,
        let Q := cylinder (region (A.normal i) 1) δ τ
        (∀ w : List (Option (RIdx n)), w.length ≤ k →
          ContinuousOn (jet Q w (pull A i u)) Q ∧
          ∀ z ∈ Q, |jet Q w (pull A i u) z| ≤ B) ∧
        ∀ ν : RIdx n, A.normal i = some ν →
          (∀ z ∈ Q, 0 < flatA h A i z ν ν) ∧
          ∀ w : List (Option (RIdx n)), w.length ≤ k → ∀ z ∈ Q,
            jet Q w (jet Q [some ν, some ν] (pull A i u)) z =
              jet Q w (normalRecovery h A i ν Q (pull A i u)) z

end Yau.F05Transport
