import spec.CHAIN.L22Consumer

/-!
Closed planning obligations for exactly the 22 active citation leaves in
`LEDGER.md`. Every declaration below has type `Prop`, with no term parameters,
implicit instances or universe parameters. All abstract spaces range over
`Type` (universe zero), which contains the actual manifold carriers, bundle
fibres, L² spaces and local rings used by this project. The imported generic
operator/ring declarations remain universe polymorphic; these consumer roots
deliberately instantiate their universes and quantify every structure.

These are definitions of unproved goals or proposed source statements. L22 is
a source-input candidate pending independent approval under D2, with separate
internal consumer targets. These definitions are not assumptions, proofs,
external axioms, or approvals. No main proof or contract imports this module.
Conjunctions include the separately required internal specializations; they do
not assert that one cited source states the whole conjunction. Source matching,
publication review and consumer-bridge proofs have separate pending states in
`LEAF_TARGETS.json` and `LEAF_LOCKS.md`.
-/

open MeasureTheory Bundle
open scoped ENNReal

namespace Yau.LeafObligations

/-- E02: local a.e. second-order differentiability of convex functions. -/
def L01 : Prop := LeafCandidates.Aleksandrov

/-- P06: the actual Hodge and Dirac core/maximal graphs, together with the
Hilbert-space inference from the square. All Hilbert data are quantified. -/
def L03 : Prop :=
  OperatorCandidates.HodgeEssentialSelfAdjointness ∧
    OperatorCandidates.DiracEssentialSelfAdjointness ∧
    ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H],
      OperatorCandidates.EssentialSelfAdjointOfSquare (H := H)

/-- E02: affine contact with a boundary gap and actual compact attainment. -/
def L04 : Prop :=
  LeafCandidates.Jensen ∧ LeafCandidates.InfConvolutionAttainment

/-- F01: generic transformed-Hessian regularity, its computed complex-Hessian
representation and the initial-surface specialization consumed by the flow. -/
def L05 : Prop :=
  ParabolicCandidates.ChuTransformedHessian ∧
    ParabolicCandidates.ComplexHessianRepresentation ∧
    ParabolicCandidates.MongeAmpereInitialSchauder

/-- P06: the wave/heat equivalence on every concrete metric-measure Bochner
L² space. This does not construct the canonical exterior-bundle realization. -/
def L06 : Prop :=
  ∀ (S E : Type) [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure S) [SigmaFinite μ],
    OperatorCandidates.WaveHeatEquivalence (E := E) μ

/-- The common solvability/metric-independence obligation of L07 and L14.
The base, rank, fibre family and every genuine Mathlib bundle instance are
quantified inside the proposition; there is no fixed unseen bundle parameter. -/
def BundleSolvability : Prop :=
  ∀ (n r : ℕ) (M : ComplexManifold n) (E : M.Carrier → Type)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
    [TopologicalSpace (TotalSpace (ComplexVector r) E)]
    [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E],
    LeafCandidates.WeightedDbarEstimate (r := r) E ∧
      LeafCandidates.TopDegreeMetricIndependence (r := r) E

/-- P03/P04/D03/C02/C03: determinant-tensor descent, computed curvature and
Nakano positivity, as well as the distinct weighted solvability obligation. -/
def L07 : Prop :=
  (∀ (n r : ℕ) (M : ComplexManifold n) (E : M.Carrier → Type)
    [∀ x, NormedAddCommGroup (E x)] [∀ x, NormedSpace ℂ (E x)]
    [∀ x, NormedSpace ℝ (E x)] [∀ x, IsScalarTower ℝ ℂ (E x)]
    [TopologicalSpace (TotalSpace (ComplexVector r) E)]
    [FiberBundle (ComplexVector r) E] [VectorBundle ℂ (ComplexVector r) E],
    LeafCandidates.TensorDetMetricDescent (r := r) E ∧
      LeafCandidates.TensorDetCurvatureIdentity (r := r) E ∧
      LeafCandidates.DemaillySkoda (r := r) E) ∧
    BundleSolvability

/-- D04 and its D02 consumer: L¹ compactness/Hartogs, the smooth-sequence
Riesz representation, and finiteness of large atoms of a locally finite measure.
No representation of an EReal-valued limiting atom uses `Real.log 0`. -/
def L08 : Prop :=
  LeafCandidates.SubharmonicL1Compactness ∧ LeafCandidates.SubharmonicHartogs ∧
    LeafCandidates.SmoothPlanarRieszDecomposition ∧ LeafCandidates.LocallyFiniteLargeAtoms

/-- D02/C02: the planar weak-gradient Morrey bound and interior H^s embedding. -/
def L09 : Prop :=
  LeafCandidates.PlanarMorrey ∧ LeafCandidates.InteriorSobolevEmbedding

/-- V02/C02: the disc Dirichlet inverse and variable-coefficient interior bound. -/
def L10 : Prop :=
  LeafCandidates.DiscDirichletEstimate ∧ LeafCandidates.InteriorEllipticEstimate

/-- P04/P05/P06: relative volume comparison in real dimension 2n. -/
def L12 : Prop := LeafCandidates.BishopGromov

/-- P03/P04/D03/C02/C03: the same precise solvability target recorded at L07.
Keeping the citation node does not create a second analytic assumption. -/
def L14 : Prop := BundleSolvability

/-- F01/F04/F05: the bootstrap and all seven LSU citation sites, the local linear bootstrap estimate,
and the concrete exterior-volume bridge needed by the boundary Hölder use. -/
def L16 : Prop :=
  ParabolicCandidates.ZeroDataEnergyExistence ∧
    ParabolicCandidates.ZeroInitialCauchySolution ∧
    ParabolicCandidates.HomogeneousInteriorSmoothing ∧
    ParabolicCandidates.CompatibleDirichletSchauder ∧
    ParabolicCandidates.UniformSmallTimeInverse ∧
    ParabolicCandidates.ExpBoundaryHolder ∧
    ParabolicCandidates.InteriorLinearSchauder ∧
    ParabolicCandidates.SmoothDomainExteriorMeasure

/-- F01: complete Hermitian bounded-geometry short-time potential flow. -/
def L17 : Prop := LeafCandidates.HermitianShortTimeFlow

/-- P04/P05: the nonnegative smooth subharmonic p=1 mean-value estimate. -/
def L18 : Prop := LeafCandidates.LiSchoenMeanValue

/-- P06/P07/F03: both differential and Gaussian scalar heat estimates. -/
def L19 : Prop := LeafCandidates.LiYauDifferential ∧ LeafCandidates.LiYauGaussian

/-- P06: finite propagation with all underlying metric/L² data quantified. -/
def L20 : Prop :=
  ∀ (S E : Type) [MetricSpace S] [MeasurableSpace S] [BorelSpace S]
    [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
    (μ : Measure S) [SigmaFinite μ],
    OperatorCandidates.McIntoshMorrisFinitePropagation (E := E) μ

/-- C02: smooth integrability of the computed almost complex structure. -/
def L21 : Prop := LeafCandidates.SmoothNewlanderNirenberg

/-- P02 source input: Greene–Wu §4, Corollary 2, first sentence, expanded in
the C⁰ fine topology. Classical strict-psh premise and two-sided error only;
the viscosity and one-sided consumer adaptations are separate internal work. -/
def L22 : Prop := LeafCandidates.RichbergApproximation

/-- C02: local tensorial curvature-derivative estimates on buffered cylinders.
The real/complex flow identification is a separate pending consumer bridge. -/
def L23 : Prop := ParabolicCandidates.LocalCurvatureDerivatives

/-- P06/F03: the kernel-gradient consequence; derivation from the local source
and L19 is internal and is not represented as a verbatim source theorem. -/
def L24 : Prop := LeafCandidates.HeatKernelGradient

/-- D03: the module Krull intersection target, including every algebraic
structure. Analytic local-ring/module construction remains a consumer bridge. -/
def L25 : Prop :=
  ∀ (R A : Type) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
    [AddCommGroup A] [Module R A] [Module.Finite R A],
    LeafCandidates.KrullIntersection R A

/-- P06: strong heat convergence with genuine varying complete Hilbert spaces,
zero extension after heat, and all fibrewise Hilbert structures quantified. -/
def L26 : Prop :=
  ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (Hj : ℕ → Type) [∀ j, NormedAddCommGroup (Hj j)]
    [∀ j, InnerProductSpace ℂ (Hj j)] [∀ j, CompleteSpace (Hj j)],
    OperatorCandidates.ExhaustionHeatConvergence (H := H) (Hj := Hj)

end Yau.LeafObligations
