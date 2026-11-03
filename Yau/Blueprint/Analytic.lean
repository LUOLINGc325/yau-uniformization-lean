import Yau.Blueprint.Stages

/-! Concrete components of the initial-data and scalar-comparison contracts.
These are propositions to prove in the proving phase, not supplied operators. -/
open scoped Manifold Topology ContDiff Matrix ComplexOrder NNReal
open MeasureTheory Filter
noncomputable section
namespace Yau.Blueprint
open Yau
variable {n : ℕ}

/-- The signed Busemann limit and its Lipschitz estimate; preliminaries.tex:53-61. -/
def BusemannConclusion (X : KahlerManifold n) (o : Pt X) : Prop :=
  ∃ ray : ℝ≥0 → Pt X, ray 0 = o ∧
    (∀ s t, distFrom X.metric.form (ray s) (ray t) = |(t : ℝ) - (s : ℝ)|) ∧
    ∃ b : Pt X → ℝ,
      (∀ x, Tendsto (fun j : ℕ =>
        distFrom X.metric.form o (ray j) - distFrom X.metric.form x (ray j)) atTop (nhds (b x))) ∧
      (∀ x y, |b x - b y| ≤ distFrom X.metric.form x y)

/-- Initial analytic data (i), preliminaries.tex:20-21. -/
def StrictPshWeight (X : KahlerManifold n) (o : Pt X) : Prop :=
  ∃ ψ : Pt X → ℝ, IsSmoothStrictPsh ψ ∧
    ∃ C : ℝ, ∀ x, ψ x ≤ C * (1 + distFrom X.metric.form o x)

/-- Initial analytic data (ii), including both jet interpolation problems. -/
def FiniteInterpolation (X : KahlerManifold n) : Prop :=
  (∀ (pts : Finset (Pt X)) (k : ℕ) (Pj : Pt X → MvPolynomial (Fin n) ℂ),
    ∃ f, IsHolomorphicFn f ∧ ∀ p ∈ pts, JetAgreeFn f p (Pj p) k) ∧
  (∀ (pts : Finset (Pt X)) (k : ℕ) (Pj : Pt X → Fin n → MvPolynomial (Fin n) ℂ),
    ∃ V : VectorField X.manifold, IsHolomorphicField V ∧
      ∀ p ∈ pts, JetAgreeField V p (Pj p) k) ∧
  (∃ (N : ℕ) (F : Pt X → ComplexVector N),
    IsHolomorphicVecMap F ∧ Function.Injective F ∧ IsImmersionMap F) ∧
  (∃ (m : ℕ) (V : Fin m → VectorField X.manifold),
    (∀ i, IsHolomorphicField (V i)) ∧
      ∀ x, Submodule.span ℂ (Set.range fun i => V i x) = ⊤)

/-- The canonical sections and Ricci majorant in initial data (iii). -/
def CanonicalInitialData (X : KahlerManifold n) (o : Pt X) : Prop :=
  (∀ x, ∃ S : CanonicalSection X.manifold, IsHolomorphicCanonical S ∧ S x ≠ 0 ∧
    ∃ C : ℝ, ∀ y,
      Real.log (canonicalNormSq X.metric.form S y) ≤ C * (1 + distFrom X.metric.form o y)) ∧
  (∃ Ξ : Pt X → ℝ, SmoothFn Ξ ∧
    (∀ x, HermLE (ricci X.metric.form x) (levi Ξ x)) ∧
    ∃ C : ℝ, ∀ x, Ξ x ≤ C * (1 + (distFrom X.metric.form o x) ^ ((3 : ℝ) / 2)))

/-- Initial data (iv), with the two-sided complex Hessian estimate. -/
def ControlledExhaustion (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ) : Prop :=
  SmoothFn u ∧ (∀ c : ℝ, IsCompact {x | u x ≤ c}) ∧
  (∀ x, 1 ≤ u x) ∧ ∃ C : ℝ, 0 < C ∧ ∀ x,
    C⁻¹ * (1 + distFrom X.metric.form o x) ≤ u x ∧
    u x ≤ C * (1 + distFrom X.metric.form o x) ∧
    gradNormSq X.metric.form u x ≤ C ^ 2 ∧
    HermLE ((-(C / u x) : ℂ) • gMat X.metric.form x) (levi u x) ∧
    HermLE (levi u x) (((C / u x : ℝ) : ℂ) • gMat X.metric.form x)

/-- Initial data (v). Neither the curvature nor the canonical norm is free data. -/
def CanonicalAverages (X : KahlerManifold n) (o : Pt X) : Prop :=
  (∀ S : CanonicalSection X.manifold, IsHolomorphicCanonical S → S o ≠ 0 →
    (∃ C : ℝ, ∀ y,
      Real.log (canonicalNormSq X.metric.form S y) ≤ C * (1 + distFrom X.metric.form o y)) →
    ∃ C : ℝ, ∀ μ, IsRiemannianVolume X.metric.form μ → ∀ L, 1 ≤ L →
      BallIntegralLE X.metric.form μ o
        (fun x => |Real.log (canonicalNormSq X.metric.form S x)|) L (C * L)) ∧
  (∃ C : ℝ, ∀ μ, IsRiemannianVolume X.metric.form μ → ∀ L, 1 ≤ L →
    BallIntegralLE X.metric.form μ o (scalarCurvature X.metric.form) L (C / L))

/-- The canonical-section growth consequence of the weighted L² estimate,
preliminaries.tex:141-156. The integrand uses the actual canonical bundle norm. -/
def CanonicalWeightedGrowth (X : KahlerManifold n) (o : Pt X) : Prop :=
  ∀ (S : CanonicalSection X.manifold) (ψ : Pt X → ℝ) (k : ℝ),
    IsHolomorphicCanonical S → S o ≠ 0 → IsSmoothStrictPsh ψ → 0 < k →
    (∃ C : ℝ, ∀ x, ψ x ≤ C * (1 + distFrom X.metric.form o x)) →
    ∀ μ, IsRiemannianVolume X.metric.form μ →
      (∫⁻ x, ENNReal.ofReal (canonicalNormSq X.metric.form S x * Real.exp (-k * ψ x)) ∂μ) < ⊤ →
      ∃ C : ℝ, ∀ x,
        canonicalNormSq X.metric.form S x ≤ Real.exp (C * (1 + distFrom X.metric.form o x))

/-- Jointly C¹ in space-time, with smooth spatial slices, including one-sided
C¹ regularity at the endpoints of I. -/
def SmoothSpaceC1Time {M : ComplexManifold n} (f : M.Carrier → ℝ → ℝ) (I : Set ℝ) : Prop :=
  (∀ t ∈ I, SmoothFn (fun x => f x t)) ∧
    ∀ x : M.Carrier, ContDiffOn ℝ 1
      (fun p : ComplexVector n × ℝ => f (chartInv x p.1) p.2) (chartTarget x ×ˢ I)

/-- Integrable comparison cutoff, flow.tex:483-493. The threshold is chosen before k. -/
def IntegrableCutoffs (X : KahlerManifold n) (o : Pt X) (h : Flow X) : Prop :=
  ∀ u : Pt X → ℝ, ControlledExhaustion X o u → ∀ T, 0 < T →
    ∃ β : ℝ, 0 < β ∧ ∃ k₀ : ℕ, ∀ k, k₀ ≤ k →
      ∃ χ : STF X, ∃ C : ℝ, 0 < C ∧
        SmoothSpaceC1Time χ (Set.Icc 0 T) ∧
        (∀ μ, IsRiemannianVolume X.metric.form μ → ∀ t ∈ Set.Icc 0 T,
          (∫⁻ x, ENNReal.ofReal (χ x t) ∂μ) < ⊤) ∧
        ∀ x t, t ∈ Set.Icc 0 T →
          0 < χ x t ∧ C⁻¹ * (u x) ^ (-(k : ℤ)) ≤ χ x t ∧
          χ x t ≤ C * (u x) ^ (-(k : ℤ)) ∧
          gradNormSq X.metric.form (fun y => χ y t) x ≤ (C * χ x t / u x) ^ 2 ∧
          HermLE (levi (fun y => χ y t) x) (((C * χ x t : ℝ) : ℂ) • gMat (h t) x) ∧
          (0 < t → deriv (χ x) t ≤ C * (1 + t ^ (β - 1)) * χ x t)

/-- The actual metric-defect average derived from the potential identity;
flow.tex:350-367. This is not the rho-average already supplied by F01. -/
def MetricDefectAverages (X : KahlerManifold n) (o : Pt X) (h : Flow X) : Prop :=
  ∀ T, 0 < T → ∃ C : ℝ, 0 < C ∧ ∀ μ, IsRiemannianVolume X.metric.form μ →
    ∀ L, 1 ≤ L → ∀ t ∈ Set.Icc 0 T,
      (∀ x, 0 ≤ traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x) ∧
        traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x) ≤ n) ∧
      BallIntegralLE X.metric.form μ o
        (fun x => traceWith (gMat X.metric.form x) (gMat X.metric.form x - gMat (h t) x))
        L (C * t / L)

/-- The positive proper supercaloric barrier, with its actual flow Laplacian. -/
def ProperSupercaloric (X : KahlerManifold n) (o : Pt X) (h : Flow X) : Prop :=
  ∀ T, 0 < T → ∃ Q : STF X, ∃ c : ℝ, 0 < c ∧
    SmoothSpaceTime Q (Set.Icc 0 T) ∧ ∀ x t, t ∈ Set.Icc 0 T →
      0 < Q x t ∧ c * (1 + distFrom X.metric.form o x ^ 2) ≤ Q x t ∧
      c * traceWith (gMat (h t) x) (gMat X.metric.form x) ≤ heatOp h (Set.Icc 0 T) Q x t

/-- Smooth majorant: the nonlinear PDE is imposed on w, not included as v=0. -/
def SmoothMajorant (X : KahlerManifold n) (h : Flow X) (ρ : STF X) : Prop :=
  ∀ T, 0 < T → ∀ v : STF X,
    UpperSemicontinuousOn (fun p : Pt X × ℝ => v p.1 p.2) (Set.univ ×ˢ Set.Icc 0 T) →
    (∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ,
      ∀ x ∈ K, ∀ t ∈ Set.Icc 0 T, |v x t| ≤ C) →
    (∀ x t, t ∈ Set.Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t) →
    NonlinearViscositySub h T v → ∃ w : STF X,
      SmoothSpaceTime w (Set.Ioo 0 T) ∧
      ContinuousOn (fun p : Pt X × ℝ => w p.1 p.2) (Set.univ ×ˢ Set.Ico 0 T) ∧
      (∀ x, w x 0 = 0) ∧ ∀ x t, t ∈ Set.Ico 0 T →
        v x t ≤ w x t ∧ w x t ≤ ρ x t ∧
        (0 < t → deriv (w x) t = Real.exp (-w x t) * laplacian (h t) (fun y => w y t) x +
          (1 - Real.exp (-w x t)) * scalarCurvature (h t) x)

end Yau.Blueprint
