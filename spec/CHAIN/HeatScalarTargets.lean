import spec.CHAIN.HeatConcreteBindings

/-! Fixed actual-metric scalar Dirichlet/exhaustion/initial-face declarations.
All are unproved predicates. No kernel, operator or desired regularity is an
independent geometric hypothesis. -/
open MeasureTheory Filter
open scoped Topology ENNReal NNReal InnerProductSpace Manifold ContDiff
noncomputable section
namespace Yau.HeatConcreteBindings
open Yau.Blueprint Yau.OperatorCandidates Yau.HeatTargetCandidates
variable {n : ℕ} {M : ComplexManifold n}

/-- Actual scalar function as a degree-zero real alternating form. -/
def scalarZeroForm (f : M.Carrier → ℝ) : RealForm M 0 :=
  fun x => ContinuousAlternatingMap.constOfIsEmpty ℝ (TangentVector M x) (Fin 0) (f x)

def ScalarL2 (μ : Measure M.Carrier) (f : M.Carrier → ℝ) : Prop :=
  AEStronglyMeasurable f μ ∧ (∫⁻ x, ENNReal.ofReal (|f x| ^ 2) ∂μ) < ⊤

def scalarL2DistanceSq (μ : Measure M.Carrier) (f h : M.Carrier → ℝ) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (|f x - h x| ^ 2) ∂μ

def ScalarTest (O : Set M.Carrier) (f : M.Carrier → ℝ) : Prop :=
  SmoothFn f ∧ HasCompactSupport f ∧ tsupport f ⊆ O

/-- Closure of the actual compact scalar d graph, with zero domain boundary.
This uses the actual one-form norm, not a separately supplied gradient. -/
def ScalarEnergyClosure (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (f : M.Carrier → ℝ) (df : RealForm M 1) : Prop :=
  ScalarL2 (μ.restrict O) f ∧ L2RealForm g (μ.restrict O) df ∧
  ∃ (fs : ℕ → M.Carrier → ℝ) (dfs : ℕ → RealForm M 1),
    (∀ j, ScalarTest O (fs j) ∧ ScalarL2 (μ.restrict O) (fs j) ∧
      SmoothRealForm (dfs j) ∧ L2RealForm g (μ.restrict O) (dfs j) ∧
      RepresentsExterior (scalarZeroForm (fs j)) (dfs j)) ∧
    Tendsto (fun j => scalarL2DistanceSq (μ.restrict O) (fs j) f +
      formL2DistanceSq g (μ.restrict O) (dfs j) df) atTop (𝓝 0)

/-- Full prequotient graph of the actual nonnegative scalar Dirichlet
Friedrichs generator -L = □₀/2, with the fixed one-half energy factor. -/
def ScalarFriedrichsPair (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (f w : M.Carrier → ℝ) : Prop :=
  ScalarL2 (μ.restrict O) w ∧ ∃ df, ScalarEnergyClosure g μ O f df ∧
    ∀ v dv, ScalarEnergyClosure g μ O v dv →
      Integrable (formInner g df dv) (μ.restrict O) ∧
      Integrable (fun x => w x * v x) (μ.restrict O) ∧
      (∫ x in O, formInner g df dv x ∂μ) / 2 = ∫ x in O, w x * v x ∂μ

/-- Actual interior smoothness in both spatial variables and heat time. -/
def KernelSmoothOn (O : Set M.Carrier)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  ∀ x y, ContDiffOn ℝ ∞
    (fun p : (ComplexVector n × ComplexVector n) × ℝ =>
      H p.2 (chartInv x p.1.1) (chartInv y p.1.2))
    (({z | z ∈ chartTarget x ∧ chartInv x z ∈ O} ×ˢ
      {z | z ∈ chartTarget y ∧ chartInv y z ∈ O}) ×ˢ Set.Ioi 0)

/-- A single kernel is chosen before every source. Its scalar generator is
identified in BOTH directions by the actual Dirichlet variational graph.
No mass-one, global representation or smoothing hypothesis is an inlet. -/
def DirichletScalarKernel (g : HermitianField M) (μ : Measure M.Carrier)
    (O : Set M.Carrier) (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  KernelSmoothOn O H ∧
  (∀ b, 0 < b → ∀ x y, 0 ≤ H b x y ∧
    (x ∈ O → y ∈ O → 0 < H b x y) ∧
    (x ∉ O ∨ y ∉ O → H b x y = 0) ∧ H b x y = H b y x) ∧
  (∀ b, 0 < b → ∀ x ∈ O, ∀ y ∈ O,
    HasDerivAt (fun s => H s x y) (laplacian g (fun z => H b z y) x) b) ∧
  (∀ b, 0 < b → ∀ y ∈ O, ∀ x ∈ frontier O,
    Tendsto (fun z => H b z y) (𝓝[O] x) (𝓝 0)) ∧
  (∀ b, 0 < b → ∀ x, Integrable (H b x) μ ∧
    (∫ y, H b x y ∂μ) ≤ 1) ∧
  (∀ b c, 0 < b → 0 < c → ∀ x y,
    Integrable (fun z => H b x z * H c z y) μ ∧
    H (b + c) x y = ∫ z, H b x z * H c z y ∂μ) ∧
  (∀ f, ScalarL2 (μ.restrict O) f →
    (∀ b, 0 < b → ∀ x ∈ O, Integrable (fun y => H b x y * f y) μ) ∧
    (∀ b, 0 < b → ScalarL2 (μ.restrict O) (boundedKernelEvolution μ H f b)) ∧
    Tendsto (fun b => scalarL2DistanceSq (μ.restrict O)
      (boundedKernelEvolution μ H f b) f) (𝓝[>] 0) (𝓝 0)) ∧
  (∀ f w, ScalarL2 (μ.restrict O) f → ScalarL2 (μ.restrict O) w →
    (ScalarFriedrichsPair g μ O f w ↔
      Tendsto (fun b => ∫⁻ x in O, ENNReal.ofReal
        (|((boundedKernelEvolution μ H f b x - f x) / b) + w x| ^ 2) ∂μ)
        (𝓝[>] 0) (𝓝 0))) ∧
  ∀ f : M.Carrier → ℝ, Continuous f → HasCompactSupport f → tsupport f ⊆ O →
    ∀ y ∈ O, Tendsto (fun b => ∫ x, H b x y * f x ∂μ) (𝓝[>] 0) (𝓝 (f y))

/-- Full local C∞ convergence on compact positive-time product cylinders. -/
def KernelLocalSmoothLimit (Hs : ℕ → ℝ → M.Carrier → M.Carrier → ℝ)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  ∀ x y (K Q : Set (ComplexVector n)), IsCompact K → IsCompact Q →
    K ⊆ chartTarget x → Q ⊆ chartTarget y → ∀ eps T, 0 < eps → eps < T →
    ∀ (m : ℕ) η, 0 < η → ∃ J, ∀ j, J ≤ j → ∀ z ∈ K, ∀ w ∈ Q,
      ∀ b ∈ Set.Icc eps T,
        ‖iteratedFDeriv ℝ m (fun p : (ComplexVector n × ComplexVector n) × ℝ =>
          Hs j p.2 (chartInv x p.1.1) (chartInv y p.1.2) -
          H p.2 (chartInv x p.1.1) (chartInv y p.1.2)) ((z, w), b)‖ < η

/-- The same extended-zero Dirichlet kernels increase to one finite H;
this is the registered minimal-exhaustion construction, before all f/u/T. -/
def MinimalExhaustionOutput (g : HermitianField M) (μ : Measure M.Carrier)
    (O : ℕ → Set M.Carrier) (Hs : ℕ → ℝ → M.Carrier → M.Carrier → ℝ)
    (H : ℝ → M.Carrier → M.Carrier → ℝ) : Prop :=
  SmoothExhaustion O ∧ (∀ j, DirichletScalarKernel g μ (O j) (Hs j)) ∧
  (∀ b, 0 < b → ∀ x y, Monotone (fun j => Hs j b x y) ∧
    Tendsto (fun j => Hs j b x y) atTop (𝓝 (H b x y))) ∧
  KernelLocalSmoothLimit Hs H ∧ MinimalKernelPositiveTimeOutput g μ H

/-- WP03-F03-DIRICHLET-KERNEL: all kernel choices are existence outputs. -/
def DirichletKernelTarget (X : KahlerManifold n) : Prop :=
  ∀ μ, IsRiemannianVolume X.metric.form μ → ∀ O : Set X.manifold.Carrier,
    SmoothPrecompactDomain O → ∃ H, DirichletScalarKernel X.metric.form μ O H

/-- WP03-F03-MINIMAL-EXHAUSTION: the actual exhaustion is input; its
kernel family and the single whole-space kernel are existence outputs. -/
def MinimalExhaustionTarget (X : KahlerManifold n) : Prop :=
  ∀ μ, IsRiemannianVolume X.metric.form μ → ∀ O : ℕ → Set X.manifold.Carrier,
    SmoothExhaustion O → ∃ Hs H, MinimalExhaustionOutput X.metric.form μ O Hs H

/-- WP03-F03-BOUNDED-INITIAL-FACE: cumulative producer output binds the
SAME domain family and minimal H, then all bounded smooth f are quantified
inside BoundedInitialFaceOutput. No representation or conservation premise. -/
def BoundedInitialFaceTarget (X : KahlerManifold n) : Prop :=
  ∀ μ, IsRiemannianVolume X.metric.form μ → ∀ O : ℕ → Set X.manifold.Carrier,
    SmoothExhaustion O → ∃ Hs H, MinimalExhaustionOutput X.metric.form μ O Hs H ∧
      BoundedInitialFaceOutput X.metric.form μ H

end Yau.HeatConcreteBindings
