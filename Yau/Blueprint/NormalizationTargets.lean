import Yau.Blueprint.HodgeContracts
import Yau.Geometry.ParabolicCalculus

/-!
Closed planning targets for the convention splice at introduction.tex:226-258.
The paper variable h is the complex coefficient metric: G = 2 Re h and
omega = 2 Im h. Every assertion below is an obligation, not an assumption
added to a metric, a heat solution, or a flow. No target is proved here.
All coordinate identities use actual chart targets; differential identities
require the displayed smoothness and, where needed, the Kähler condition.
-/
open scoped Manifold Topology ContDiff Matrix ComplexOrder ENNReal
open MeasureTheory
noncomputable section
namespace Yau.Blueprint
open Yau
variable {n : ℕ} {M : ComplexManifold n}

/-- Real scalar Laplace--Beltrami calculator in a fixed chart. The derivative
of the scalar is differentiated in that same chart, including the connection
term; this is not defined by rescaling the complex Laplacian. -/
def realLaplacianInChart (h : HermitianField M) (x : M.Carrier)
    (f : M.Carrier → ℝ) (z : ComplexVector n) : ℝ :=
  ∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b *
    (rDeriv (fun w => rDeriv (inChart x f) w b) z a -
      ∑ c, christoffel h x z c a b * rDeriv (inChart x f) z c)

/-- Scalar curvature obtained by tracing the independently computed real
Levi-Civita Ricci tensor with G inverse. -/
def realScalarCurvatureInChart (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) : ℝ :=
  ∑ a, ∑ b, (realMetricFn h x z)⁻¹ a b * realRicciCoeff h x z a b

/-- The complex Ricci matrix in the fixed chart, without re-centring the
chart inside the differentiated log determinant. -/
def ricciInChart (h : HermitianField M) (x : M.Carrier)
    (z : ComplexVector n) : Matrix (Fin n) (Fin n) ℂ :=
  -leviC (logDet h x) z

/-- Tangent reconstruction and the symmetric real-matrix iota use the same
Gram convention. The form iota is separately 2 Im, not this symmetric matrix. -/
def PaperMetricTensorNormalization (h : HermitianField M) : Prop :=
  (∀ x z, z ∈ chartTarget x →
    realMetricFn h x z = (2 : ℝ) • (Parabolic.iota (hMat h x z) : Parabolic.Mat n)) ∧
  (∀ (x : M.Carrier) (u v : TangentVector M x),
    (∑ a, ∑ b, realMetricFn h x (chartPt x x) a b *
      realCoord (tangentCoords x x u) a * realCoord (tangentCoords x x v) b) =
        2 * ((h x).toFun u v).re) ∧
  (∀ (x : M.Carrier) (u v : TangentVector M x),
    (∑ a, ∑ b, kahlerFormFn h x (chartPt x x) a b *
      realCoord (tangentCoords x x u) a * realCoord (tangentCoords x x v) b) =
        2 * ((h x).toFun u v).im)

/-- The volume density is 2^n det(h) for every measure satisfying the actual
Riemannian chart law. Existence and uniqueness of that measure are G02. -/
def PaperVolumeMeasureNormalization (h : HermitianField M) : Prop :=
  ∀ μ, IsRiemannianVolume h μ → ∀ x (s : Set M.Carrier), MeasurableSet s →
    s ⊆ (extChartAt (ComplexModel n) x).source →
    μ s = ∫⁻ z in chartPt x '' s,
      ENNReal.ofReal ((2 : ℝ) ^ n * (hMat h x z).det.re) ∂lebesgueC n

/-- Real gradient squared is twice the complex (1,0)-gradient squared. -/
def PaperGradientNormalization (h : HermitianField M) : Prop :=
  ∀ f : M.Carrier → ℝ, SmoothFn f → ∀ x,
    realGradientNormSq h f x = 2 * gradNormSq h f x

/-- Algebraic metric, length, volume, cotangent, gradient and disc splices.
No completeness, curvature bound, or positivity assumption is added. -/
def PaperMetricNormalizationTarget : Prop :=
  ∀ n (M : ComplexManifold n) (h : HermitianField M), MetricSmooth h →
    PaperMetricTensorNormalization h ∧ PaperLengthNormalization h ∧
    PaperVolumeNormalization h ∧ PaperVolumeMeasureNormalization h ∧
    PaperDualNormNormalization h ∧ PaperGradientNormalization h ∧
    PaperDiscAreaNormalization h

/-- Basic and Calculus compute the same Chern tensor. Smoothness is required
when interchanging the two Wirtinger derivative orders. -/
def ChernCalculatorCompatibility (h : HermitianField M) : Prop :=
  ∀ x i j k l, curvatureComponent h x i j k l = chernCurvature h x i j k l

/-- Shared central-chart Ricci target, previously isolated in the candidate
leaf file. Ric_real = 2 iota_R(Ric_h), for G = 2 Re h. -/
def KahlerRealRicciIdentification : Prop :=
  ∀ n (M : ComplexManifold n) (h : HermitianField M),
    MetricSmooth h → KahlerClosed h → ∀ x a b,
      realRicciCoeff h x (chartPt x x) a b =
        2 * (Parabolic.iota (ricci h x) : Parabolic.Mat n) a b

/-- The same identification on every chart target, plus the scalar trace
factor R_real = 2 R_h at the represented manifold point. -/
def PaperRicciChartNormalization (h : HermitianField M) : Prop :=
  (∀ x z, z ∈ chartTarget x → ∀ a b,
    realRicciCoeff h x z a b =
      2 * (Parabolic.iota (ricciInChart h x z) : Parabolic.Mat n) a b) ∧
  (∀ x z, z ∈ chartTarget x →
    realScalarCurvatureInChart h x z = 2 * scalarCurvature h (chartInv x z))

/-- The normalized curvature is the same Chern ratio; the real numerator is
four times the complex numerator and each real squared length is twice h.
This also connects the Basic calculator to the Calculus positivity predicate. -/
def PaperBisectionalNormalization (h : HermitianField M) : Prop :=
  PaperChernCurvatureNormalization h ∧ ChernCalculatorCompatibility h ∧
  (∀ x (u v : TangentVector M x),
    paperHolomorphicBisectionalCurvature h x u v =
      ChernBisectionalCurvatureOnTangent h x u v) ∧
  (∀ x (u v : TangentVector M x),
    paperBisectionalNumerator h x u v =
      4 * bisectionalForm h x (tangentCoordinates x u) (tangentCoordinates x v)) ∧
  (PaperPositiveBisectional h ↔ GriffithsPositive h)

/-- In complex dimension one, evaluate Gaussian curvature on the genuine
nondegenerate plane (u,Ju). The other vector v need only be nonzero. -/
def PaperSurfaceCurvatureNormalization : Prop :=
  ∀ (M : ComplexManifold 1) (h : HermitianField M),
    MetricSmooth h → KahlerClosed h → ∀ x (u v : TangentVector M x),
    u ≠ 0 → v ≠ 0 →
      paperHolomorphicBisectionalCurvature h x u v =
        paperRm h x u (Complex.I • u) (Complex.I • u) u /
          (2 * hermitianNormSq (h x) u) ^ 2

def PaperCurvatureNormalizationTarget : Prop :=
  (∀ n (M : ComplexManifold n) (h : HermitianField M),
    MetricSmooth h → KahlerClosed h →
      PaperBisectionalNormalization h ∧ PaperRicciChartNormalization h) ∧
  KahlerRealRicciIdentification ∧ PaperSurfaceCurvatureNormalization

/-- The positive-sign real scalar Laplacian is twice the paper Laplacian,
on every chart. This links the independent real connection to complex heat. -/
def PaperScalarLaplacianNormalization (h : HermitianField M) : Prop :=
  ∀ f : M.Carrier → ℝ, SmoothFn f → ∀ x z, z ∈ chartTarget x →
    realLaplacianInChart h x f z = 2 * laplacian h f (chartInv x z)

/-- Smoothness and global chart reconstruction for the actual Kähler/Ricci
forms and dd of an arbitrary smooth real function. The arbitrary pointwise inverse
in OneOneRepresentationBridge does not by itself establish these statements. -/
def PaperKahlerLeviFormNormalization (h : HermitianField M) : Prop :=
  (∃ omega : RealForm M 2, SmoothRealForm omega ∧ RealOneOne omega ∧
    ClosedRealForm omega ∧ RepresentsIota (gMat h) omega ∧
    ∀ x z, z ∈ chartTarget x → ∀ I,
      formComponents omega x z I = kahlerFormFn h x z (I 0) (I 1)) ∧
  (∀ f : M.Carrier → ℝ, SmoothFn f →
    ∃ A : RealForm M 2, SmoothRealForm A ∧ RealOneOne A ∧
      ClosedRealForm A ∧ RepresentsIota (levi f) A ∧
      ∀ x z, z ∈ chartTarget x → ∀ I,
        formComponents A x z I =
          2 * (∑ a, ∑ b, star (realVec (I 0) a) *
            leviC (inChart x f) z a b * realVec (I 1) b).im) ∧
  (∃ rho : RealForm M 2, SmoothRealForm rho ∧ RealOneOne rho ∧
    ClosedRealForm rho ∧ RepresentsIota (ricci h) rho ∧
    ∀ x z, z ∈ chartTarget x → ∀ I,
      formComponents rho x z I =
        2 * (∑ a, ∑ b, star (realVec (I 0) a) *
          ricciInChart h x z a b * realVec (I 1) b).im)

/-- Exact norm conversion for every signed real (1,1) form. In particular
omega has squared real norm n; no unmentioned factor enters the heat class. -/
def PaperOneOneNormNormalization (h : HermitianField M) : Prop :=
  ∀ A : RealForm M 2, RealOneOne A → ∀ x,
    formNormSq h A x =
      (Matrix.trace (((gMat h x)⁻¹ * formHermitianMatrix A x) ^ 2)).re

/-- General geometric Hodge splice. No boundedness, closedness or curvature
sign is imposed on the metric, beyond smooth Kähler; closedness of the input
form appears exactly in the second identity of HodgeNormalization. -/
def PaperHodgeNormalizationTarget : Prop :=
  ∀ n (M : ComplexManifold n) (h : HermitianField M),
    MetricSmooth h → KahlerClosed h →
      FormCalculusRealization h ∧ HodgeNormalization h ∧
      OneOneRepresentationBridge h ∧ HodgeTraceDataBridge h ∧
      PaperScalarLaplacianNormalization h ∧
      PaperKahlerLeviFormNormalization h ∧ PaperOneOneNormNormalization h

/-- Shared flow target: the paper time satisfies dG/dt = -Ric_real (sigma=1).
The initial time is included through the existing within-derivative predicate. -/
def KahlerFlowRealNormalization : Prop :=
  ∀ n (M : ComplexManifold n) (g : HermitianField M) (h : ℝ → HermitianField M),
    IsKahlerRicciFlow g h → LocalRealRicciFlow h Set.univ (Set.Ici 0) 1

/-- Standard Ricci-flow time is tau=t/2: G_standard(tau)=G_paper(2*tau).
This is an actual flow predicate, including regularity and the endpoint. -/
def KahlerFlowStandardTimeNormalization : Prop :=
  ∀ n (M : ComplexManifold n) (g : HermitianField M) (h : ℝ → HermitianField M),
    IsKahlerRicciFlow g h →
      LocalRealRicciFlow (fun tau => h (2 * tau)) Set.univ (Set.Ici 0) 2

/-- The actual real Hessian of a C2 function gives its complex Hessian under
the 1/4 J-invariant projection. This target is shared with parabolic leaves. -/
def ComplexHessianRepresentation : Prop :=
  ∀ n (u : ComplexVector n → ℝ) x, ContDiffAt ℝ 2 u x →
    Parabolic.complexHessianMap
      (Parabolic.hessian (fun p : Parabolic.Point n => u p.1) (x, 0)) =
        Parabolic.iota (leviC u x)

/-- Symmetric realification used by the real parabolic equation. Positivity
is needed precisely at log determinant and inverse metric; A may be signed.
These formulas use iota_R(H), whereas the Riemannian matrix is 2 iota_R(H). -/
def PaperParabolicMatrixNormalizationTarget : Prop :=
  ComplexHessianRepresentation ∧
  ∀ n (H : Matrix (Fin n) (Fin n) ℂ), H.PosDef →
    Parabolic.logDetReal (Parabolic.iota H) = Real.log H.det.re ∧
    ∀ A : Matrix (Fin n) (Fin n) ℂ, A.IsHermitian →
      Matrix.trace ((Parabolic.iota H : Parabolic.Mat n)⁻¹ *
        (Parabolic.iota A : Parabolic.Mat n)) = 2 * traceWith H A

def PaperFlowNormalizationTarget : Prop :=
  KahlerRealRicciIdentification ∧ KahlerFlowRealNormalization ∧
    KahlerFlowStandardTimeNormalization ∧ PaperParabolicMatrixNormalizationTarget

/-- Complete convention-splice obligation. This closed Prop is suitable for
a blueprint node; it is neither a theorem nor a new field of any input object. -/
def PaperNormalizationTarget : Prop :=
  PaperMetricNormalizationTarget ∧ PaperCurvatureNormalizationTarget ∧
    PaperHodgeNormalizationTarget ∧ PaperFlowNormalizationTarget

end Yau.Blueprint
