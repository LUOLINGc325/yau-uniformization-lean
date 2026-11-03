import Yau.Geometry.DifferentialForms

/-! P06 targets, planning only. These definitions neither construct a heat map
nor certify any target. The bounded smooth scope is intentional; measurable
initial data, cutoff limits and the complete L² construction remain separate
obligations. All equations use G=2 Re h, its Riemannian volume, and -□/2. -/
open scoped Manifold Topology ContDiff ComplexOrder ENNReal
open MeasureTheory Filter
noncomputable section
namespace Yau.Blueprint
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- C∞ spatial convergence on every compact inside each coordinate target. -/
def FormSmoothInitial {k : ℕ} (U : ℝ → RealForm M k) (A : RealForm M k) : Prop :=
  U 0 = A ∧ ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
    ∀ (j : ℕ) (I : Fin k → RIdx n) ε, 0 < ε → ∃ τ > 0, ∀ t, 0 < t → t < τ →
      ∀ z ∈ K, ‖iteratedFDeriv ℝ j (fun w =>
        formComponents (U t) x w I - formComponents A x w I) z‖ < ε

/-- Finite-time uniform metric norm, including arbitrarily small positive times.
On real (1,1) forms this is equivalent to the ±B_T g class, with changed
constants. The equivalence is a target below, not a presumed normalization. -/
def BoundedFormHeatClass {k : ℕ} (g : HermitianField M) (U : ℝ → RealForm M k) : Prop :=
  ∀ T, 0 < T → ∃ B : ℝ, 0 < B ∧ ∀ x t, 0 < t → t ≤ T →
    formNormSq g (U t) x ≤ B ^ 2

/-- Coefficient PDE at every point of every chart, not merely a chosen frame. -/
def FormHeatEquation {k : ℕ} (g : HermitianField M) (U : ℝ → RealForm M k) : Prop :=
  ∀ x z, z ∈ chartTarget x → ∀ t, 0 < t → ∀ I,
    HasDerivAt (fun s => formComponents (U s) x z I)
      (hodgeGeneratorComponents g x (formComponents (U t) x) z I) t

def IsBoundedFormHeat {k : ℕ} (g : HermitianField M)
    (A : RealForm M k) (U : ℝ → RealForm M k) : Prop :=
  SmoothFormTime U (Set.Ioi 0) ∧ FormSmoothInitial U A ∧
    BoundedFormHeatClass g U ∧ FormHeatEquation g U

def ScalarSmoothInitial (u : ℝ → M.Carrier → ℝ) (f : M.Carrier → ℝ) : Prop :=
  u 0 = f ∧ ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
    ∀ (j : ℕ) ε, 0 < ε → ∃ τ > 0, ∀ t, 0 < t → t < τ → ∀ z ∈ K,
      ‖iteratedFDeriv ℝ j (fun w => inChart x (u t) w - inChart x f w) z‖ < ε

def IsBoundedScalarHeat (g : HermitianField M) (f : M.Carrier → ℝ)
    (u : ℝ → M.Carrier → ℝ) : Prop :=
  SmoothSpaceTime (fun x t => u t x) (Set.Ioi 0) ∧ ScalarSmoothInitial u f ∧
    (∀ T, 0 < T → ∃ B : ℝ, 0 < B ∧ ∀ x t, 0 < t → t ≤ T → |u t x| ≤ B) ∧
    ∀ x t, 0 < t → HasDerivAt (fun s => u s x) (laplacian g (u t) x) t

/-- Coordinate reconstruction and compatibility, still to be proved. -/
def FormCalculusRealization (g : HermitianField M) : Prop :=
  (∀ k (A : RealForm M k), SmoothRealForm A →
    ∃ B, SmoothRealForm B ∧ RepresentsExterior A B) ∧
  (∀ k (A : RealForm M (k + 1)), SmoothRealForm A →
    ∃ B, SmoothRealForm B ∧ RepresentsCodifferential g A B) ∧
  (∀ k (A : RealForm M k), SmoothRealForm A →
    ∃ B, SmoothRealForm B ∧ RepresentsHodge g A B)

/-- The two normalization identities needed by P06. They are not assumptions
in the heat solution predicate and have not been proved here. -/
def HodgeNormalization (g : HermitianField M) : Prop :=
  (∀ f : M.Carrier → ℝ, SmoothFn f → ∀ x z, z ∈ chartTarget x →
    hodgeGeneratorComponents g x (fun w (_ : Fin 0 → RIdx n) => inChart x f w)
      z (Fin.elim0) = laplacian g f (chartInv x z)) ∧
  (∀ (A B : RealForm M 2), SmoothRealForm A → RealOneOne A → ClosedRealForm A →
    RepresentsHodge g A B → ∀ x,
      (- (1 / 2 : ℂ)) • formHermitianMatrix B x = levi (formTrace g A) x)

/-- Both inverse directions for arbitrary signed Hermitian forms (in every
dimension), and the precise infinity class. Matrix-to-form reconstruction here
is pointwise; its smoothness and chart compatibility still require separate
infrastructure. -/
def OneOneRepresentationBridge (g : HermitianField M) : Prop :=
  (∀ A : RealForm M 2, RealOneOne A →
    RepresentsIota (formHermitianMatrix A) A ∧ ∀ x, (formHermitianMatrix A x).IsHermitian) ∧
  (∀ A : M.Carrier → Matrix (Fin n) (Fin n) ℂ, (∀ x, (A x).IsHermitian) →
    ∃ α : RealForm M 2, RealOneOne α ∧ RepresentsIota A α ∧
      ∀ x, formHermitianMatrix α x = A x) ∧
  (∃ omegaForm : RealForm M 2, SmoothRealForm omegaForm ∧ RealOneOne omegaForm ∧
    RepresentsIota (gMat g) omegaForm) ∧
  (∀ U : ℝ → RealForm M 2, (∀ t, 0 < t → RealOneOne (U t)) →
    (BoundedFormHeatClass g U ↔
      ∀ T, 0 < T → ∃ B : ℝ, 0 < B ∧ ∀ t, 0 < t → t ≤ T → FormOrderBound g B (U t)))

/-- Initial scope only: smooth bounded real (1,1), not necessarily closed. -/
def BoundedOneOneData (g : HermitianField M) (A : RealForm M 2) : Prop :=
  SmoothRealForm A ∧ RealOneOne A ∧ ∃ C : ℝ, 0 ≤ C ∧ FormOrderBound g C A

/-- Side conditions needed to apply scalar existence to the actual trace. -/
def HodgeTraceDataBridge (g : HermitianField M) : Prop :=
  (∀ A : RealForm M 2, SmoothRealForm A → RealOneOne A → SmoothFn (formTrace g A)) ∧
  (∀ (A : RealForm M 2) (C : ℝ), RealOneOne A → 0 ≤ C → FormOrderBound g C A →
    ∀ x, |formTrace g A x| ≤ n * C)

/-- PDE existence and uniqueness in the stated infinity class. No arbitrary
map is supplied as input. Equality is required only on nonnegative times. -/
def HodgeHeatExistenceUniqueness (g : HermitianField M) : Prop :=
  ∀ A : RealForm M 2, BoundedOneOneData g A →
    (∃ U, IsBoundedFormHeat g A U) ∧
    ∀ U V, IsBoundedFormHeat g A U → IsBoundedFormHeat g A V →
      ∀ t, 0 ≤ t → U t = V t

def ScalarHeatExistenceUniqueness (g : HermitianField M) : Prop :=
  ∀ f : M.Carrier → ℝ, SmoothFn f → (∃ C : ℝ, ∀ x, |f x| ≤ C) →
    (∃ u, IsBoundedScalarHeat g f u) ∧
    ∀ u v, IsBoundedScalarHeat g f u → IsBoundedScalarHeat g f v →
      ∀ t, 0 ≤ t → u t = v t

/-- Separate geometric conclusions: none is hidden in `IsBoundedFormHeat`. -/
def HodgeTypeAndOrder (g : HermitianField M) : Prop :=
  (∀ A U, BoundedOneOneData g A → IsBoundedFormHeat g A U →
    ∀ t, 0 < t → RealOneOne (U t)) ∧
  (∀ A B U V, BoundedOneOneData g A → BoundedOneOneData g B →
    IsBoundedFormHeat g A U → IsBoundedFormHeat g B V → FormLE A B →
    ∀ t, 0 < t → FormLE (U t) (V t)) ∧
  (∀ A U C, BoundedOneOneData g A → IsBoundedFormHeat g A U →
    0 ≤ C → FormOrderBound g C A → ∀ t, 0 < t → FormOrderBound g C (U t))

def HodgeTraceCommutation (g : HermitianField M) : Prop :=
  ∀ A U u, BoundedOneOneData g A → IsBoundedFormHeat g A U →
    IsBoundedScalarHeat g (formTrace g A) u →
    ∀ t, 0 < t → ∀ x, formTrace g (U t) x = u t x

/-- Time translation/semigroup law, expressed entirely through PDE solutions. -/
def HodgeSemigroupLaw (g : HermitianField M) : Prop :=
  ∀ A U, BoundedOneOneData g A → IsBoundedFormHeat g A U →
    ∀ s, 0 ≤ s → ∀ V, IsBoundedFormHeat g (U s) V →
      ∀ t, 0 ≤ t → V t = U (s + t)

/-- Smooth closed case of preliminaries.tex:259-261, with an actual scalar
solution and actual interval integral. Closedness is a separate conclusion. -/
def HodgeClosedPotential (g : HermitianField M) : Prop :=
  ∀ A U u, BoundedOneOneData g A → ClosedRealForm A → IsBoundedFormHeat g A U →
    IsBoundedScalarHeat g (formTrace g A) u → ∀ t, 0 < t →
      ClosedRealForm (U t) ∧
      (∀ x, IntervalIntegrable (fun s => u s x) volume 0 t) ∧
      ∀ x, formHermitianMatrix (U t) x = formHermitianMatrix A x +
        levi (fun y => ∫ s in (0 : ℝ)..t, u s y) x

/-! Remaining implementation targets, with concrete prequotient domains.
No arbitrary semigroup or flag is used to stand in for these obligations. -/

/-- Uniqueness of weak derivatives and the variational operator, plus its
resolvent range condition. Self-adjoint quotient realization/spectral calculus
still require construction; these assertions alone do not provide that API. -/
def HodgeFormDomainTarget (g : HermitianField M) (μ : Measure M.Carrier) : Prop :=
  (∀ A dA deltaA dB deltaB,
    HodgeFormGraphClosure g μ A dA deltaA → HodgeFormGraphClosure g μ A dB deltaB →
      (∀ᵐ x ∂μ, dA x = dB x) ∧ (∀ᵐ x ∂μ, deltaA x = deltaB x)) ∧
  (∀ A W Z, FriedrichsHodgeRelation g μ A W → FriedrichsHodgeRelation g μ A Z →
    ∀ᵐ x ∂μ, W x = Z x) ∧
  (∀ (f : RealForm M 2) (lam : ℝ), L2RealForm g μ f → 0 < lam →
    ∃ A W, FriedrichsHodgeRelation g μ A W ∧ ∀ᵐ x ∂μ, W x + lam • A x = f x) ∧
  (∀ A W, SmoothRealForm A → SmoothRealForm W → CompactlySupportedRealForm A →
    FriedrichsHodgeRelation g μ A W → RepresentsHodge g A W) ∧
  (∀ A, SmoothRealForm A → CompactlySupportedRealForm A →
    ∃ W, SmoothRealForm W ∧ RepresentsHodge g A W ∧ FriedrichsHodgeRelation g μ A W)

/-- Complete L² heat characterized by the same computed PDE, bounded L² norm
on finite time intervals and L² initial convergence. Smooth initial convergence
is not demanded for rough L² data. -/
def IsL2FormHeat (g : HermitianField M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (U : ℝ → RealForm M 2) : Prop :=
  L2RealForm g μ A ∧ U 0 = A ∧ SmoothFormTime U (Set.Ioi 0) ∧ FormHeatEquation g U ∧
    (∀ t, 0 < t → L2RealForm g μ (U t)) ∧
    Tendsto (fun t => formL2DistanceSq g μ (U t) A) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) ∧
    ∀ T, 0 < T → ∃ B : ℝ, 0 < B ∧ ∀ t, 0 < t → t ≤ T →
      (∫⁻ x, ENNReal.ofReal (formNormSq g (U t) x) ∂μ) ≤ ENNReal.ofReal B

/-- The L² heat construction and uniqueness, not a choice of an evolution map. -/
def L2HodgeHeatTarget (g : HermitianField M) (μ : Measure M.Carrier) : Prop :=
  ∀ A : RealForm M 2, L2RealForm g μ A →
    (∃ U, IsL2FormHeat g μ A U) ∧
    ∀ U V, IsL2FormHeat g μ A U → IsL2FormHeat g μ A V →
      ∀ t, 0 < t → U t = V t

/-- Real |dχ|²_G, with no Wirtinger factor absorbed into the cutoff constant. -/
def realGradientNormSq (g : HermitianField M) (χ : M.Carrier → ℝ) (x : M.Carrier) : ℝ :=
  ∑ a, ∑ b, (realMetricFn g x (chartPt x x))⁻¹ a b *
    rDeriv (inChart x χ) (chartPt x x) a * rDeriv (inChart x χ) (chartPt x x) b

/-- Integer-radius smooth metric cutoffs; j=0 is not used. -/
def MetricCutoffFamily (g : HermitianField M) (o : M.Carrier)
    (χ : ℕ → M.Carrier → ℝ) : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ j : ℕ, 1 ≤ j → SmoothFn (χ j) ∧ HasCompactSupport (χ j) ∧
    (∀ x, 0 ≤ χ j x ∧ χ j x ≤ 1) ∧
    (∀ x ∈ distBall g o j, χ j x = 1) ∧
    tsupport (χ j) ⊆ distBall g o (2 * j) ∧
    ∀ x, realGradientNormSq g (χ j) x ≤ (c / j) ^ 2

/-- Full space-time C∞ convergence on compact coordinate cylinders away from 0. -/
def FormHeatLocalSmoothLimit (Us : ℕ → ℝ → RealForm M 2)
    (U : ℝ → RealForm M 2) : Prop :=
  ∀ x (K : Set (ComplexVector n)), IsCompact K → K ⊆ chartTarget x →
    ∀ eps T, 0 < eps → eps < T → ∀ (m : ℕ) (I : Fin 2 → RIdx n) η, 0 < η →
      ∃ J, ∀ j, J ≤ j → ∀ z ∈ K, ∀ t ∈ Set.Icc eps T,
        ‖iteratedFDeriv ℝ m (fun p : ComplexVector n × ℝ =>
          formComponents (Us j p.2) x p.1 I - formComponents (U p.2) x p.1 I) (z, t)‖ < η

/-- Well-defined non-L² evolution by cutoffs in the current smooth bounded
scope. Quantifying over every cutoff/basepoint and every L² evolution makes
independence a genuine conclusion once uniqueness is proved. -/
def HodgeCutoffConstruction (g : HermitianField M) (μ : Measure M.Carrier) : Prop :=
  (∀ o, ∃ χ, MetricCutoffFamily g o χ) ∧
  ∀ A : RealForm M 2, BoundedOneOneData g A →
    ∃ U, IsBoundedFormHeat g A U ∧ ∀ o χ, MetricCutoffFamily g o χ →
      (∀ j, 1 ≤ j → L2RealForm g μ (fun x => χ j x • A x)) ∧
      (∃ Us : ℕ → ℝ → RealForm M 2,
        ∀ j, 1 ≤ j → IsL2FormHeat g μ (fun x => χ j x • A x) (Us j)) ∧
      ∀ Us : ℕ → ℝ → RealForm M 2,
        (∀ j, 1 ≤ j → IsL2FormHeat g μ (fun x => χ j x • A x) (Us j)) →
        FormHeatLocalSmoothLimit Us U

/-- Smooth bounded P06 target. Completeness/Kähler are already part of X;
nonnegative real Levi-Civita HBC is the explicit geometric hypothesis. -/
def HodgeSmoothBoundedTarget (X : KahlerManifold n) : Prop :=
  (∀ x u v, 0 ≤ paperHolomorphicBisectionalCurvature X.metric.form x u v) →
  FormCalculusRealization X.metric.form ∧ HodgeNormalization X.metric.form ∧
  OneOneRepresentationBridge X.metric.form ∧ HodgeTraceDataBridge X.metric.form ∧
  HodgeHeatExistenceUniqueness X.metric.form ∧ ScalarHeatExistenceUniqueness X.metric.form ∧
  HodgeTypeAndOrder X.metric.form ∧ HodgeTraceCommutation X.metric.form ∧
  HodgeSemigroupLaw X.metric.form ∧
  HodgeClosedPotential X.metric.form ∧
  ∀ μ, IsRiemannianVolume X.metric.form μ →
    HodgeFormDomainTarget X.metric.form μ ∧ L2HodgeHeatTarget X.metric.form μ ∧
      HodgeCutoffConstruction X.metric.form μ

end Yau.Blueprint
