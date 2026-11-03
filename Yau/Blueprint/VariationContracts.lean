import Yau.Blueprint.DiscFrames

/-!
Planning definitions for variation.tex. A localization stores functions only;
its analytic requirements are explicit predicates. In particular the energy,
boundary Hessian, negative part and clock are computed expressions, never
input fields. The approximation order is ν, then ε↓0, then δ↓0, then j→∞.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint
open Yau
variable {n q : ℕ} {X : KahlerManifold n}

/-- At positive physical time the right-time operator is the ordinary
derivative, without any assumption on the negative-time values of `f`. -/
theorem physicalTime_derivWithin_eq_deriv (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) :
    derivWithin f (Set.Ici 0) t = deriv f t :=
  derivWithin_of_mem_nhds (Ici_mem_nhds ht)

/-- Actual one-sided differentiability gives ordinary differentiability at
positive time. At zero only the within derivative is asserted. -/
theorem physicalTime_hasDerivAt (f : ℝ → ℝ) {v t : ℝ} (ht : 0 < t)
    (hf : HasDerivWithinAt f v (Set.Ici 0) t) : HasDerivAt f v t :=
  hf.hasDerivAt (Ici_mem_nhds ht)

/-- All fields are concrete geometric data. `j` denotes the paper index `j+1`. -/
structure VariationData (X : KahlerManifold n) (q : ℕ) where
  o : Pt X
  h : Flow X
  U : STF X
  P : STF X
  rho : STF X
  Q : STF X
  rhoTail : ℕ → STF X
  u : Pt X → ℝ
  A : ℕ → ℝ
  B : ℕ → ℝ
  profileBase : ℝ → ℝ
  profileFiber : ℝ → ℝ
  G : CotangentPoint X.manifold → ComplexVector q
  T : ℝ
  extendedT : ℝ
  chart : Pt X
  cylinderCenter : CotangentCoord n
  cylinderRadius : ℝ
  cylinderTimeLo : ℝ
  cylinderTimeHi : ℝ
  contact : CotangentCoord n × ℝ
  test : CotangentPoint X.manifold → ℝ → ℝ

/-- A compact coordinate cylinder is derived from its center, radius and
time endpoints. No set-valued field is admitted. -/
def centerCylinder (d : VariationData X q) : Set (CotangentCoord n × ℝ) :=
  Metric.closedBall d.cylinderCenter d.cylinderRadius ×ˢ
    Set.Icc d.cylinderTimeLo d.cylinderTimeHi

def baseCost (d : VariationData X q) (j : ℕ) (x : Pt X) (t : ℝ) : ℝ :=
  ((j + 1 : ℕ) : ℝ)⁻¹ * d.Q x t + d.rhoTail j x t

def deltaBase (d : VariationData X q) (j : ℕ) (x : Pt X) : ℝ :=
  d.profileBase (d.u x / d.A j)

def deltaFiber (d : VariationData X q) (j : ℕ) (y : CotangentPoint X.manifold) : ℝ :=
  d.profileFiber (dualNorm (d.h 0) y.1 y.2 / d.B j ^ 2)

def wallBase (d : VariationData X q) (j : ℕ) (x : Pt X) : ℝ :=
  (deltaBase d j x)⁻¹ - 1

def wallFiber (d : VariationData X q) (j : ℕ) (y : CotangentPoint X.manifold) : ℝ :=
  (deltaFiber d j y)⁻¹ - 1

def wallProduct (d : VariationData X q) (j : ℕ) (y : CotangentPoint X.manifold) : ℝ :=
  deltaBase d j y.1 * deltaFiber d j y

def wallCost (d : VariationData X q) (j : ℕ) (y : CotangentPoint X.manifold) (t s : ℝ) : ℝ :=
  baseCost d j y.1 t + (1 + s) * (wallBase d j y.1 + wallFiber d j y)

def boundaryRegion (d : VariationData X q) (j : ℕ) : Set (CotangentPoint X.manifold) :=
  {y | d.u y.1 < d.A j ∧ dualNorm (d.h 0) y.1 y.2 < d.B j ^ 2}

def boundaryCompact (d : VariationData X q) (j : ℕ) : Set (CotangentPoint X.manifold) :=
  {y | d.u y.1 ≤ d.A j ∧ dualNorm (d.h 0) y.1 y.2 ≤ d.B j ^ 2}

/-- Positive profiles are required on precisely the source's open region;
the reciprocal is never used as a zero-wall shortcut outside it. -/
def WallProfiles (d : VariationData X q) : Prop :=
  ContDiff ℝ ∞ d.profileBase ∧ ContDiff ℝ ∞ d.profileFiber ∧
  (∀ r, 0 ≤ d.profileBase r ∧ d.profileBase r ≤ 1 ∧
    (0 < d.profileBase r ↔ r < 1) ∧ (r ≤ 2 / 3 → d.profileBase r = 1)) ∧
  (∀ r, 0 ≤ d.profileFiber r ∧ d.profileFiber r ≤ 1 ∧
    (0 < d.profileFiber r ↔ r < 1) ∧ (r ≤ 1 / 2 → d.profileFiber r = 1))

def StrictEnvelopeContact (d : VariationData X q) : Prop :=
  IsCompact (centerCylinder d) ∧ d.contact ∈ interior (centerCylinder d) ∧
  (centerCylinder d) ⊆ cotangentTarget d.chart ×ˢ Set.Ioo 0 d.T ∧
  (∀ p ∈ (centerCylinder d), (d.test (cotangentChartInv d.chart p.1) p.2 : EReal) ≤
    envelopeChart d.h d.T d.chart (p.1.1, p.1.2, p.2)) ∧
  (∀ p ∈ (centerCylinder d),
    (d.test (cotangentChartInv d.chart p.1) p.2 : EReal) =
      envelopeChart d.h d.T d.chart (p.1.1, p.1.2, p.2) ↔ p = d.contact) ∧
  (∃ gap : ℝ, 0 < gap ∧ ∀ p ∈ frontier (centerCylinder d),
    ((d.test (cotangentChartInv d.chart p.1) p.2 + gap : ℝ) : EReal) ≤
      envelopeChart d.h d.T d.chart (p.1.1, p.1.2, p.2)) ∧
  ∃ V : Set (CotangentCoord n × ℝ), IsOpen V ∧ centerCylinder d ⊆ V ∧
    V ⊆ cotangentTarget d.chart ×ˢ Set.Ioo 0 d.T ∧
    ContDiffOn ℝ ∞ (fun p : CotangentCoord n × ℝ =>
      d.test (cotangentChartInv d.chart p.1) p.2) V

/-- Exact setup from variation.tex:49-87. It contains only incoming
localization hypotheses, not the conclusions about infima or deformations. -/
def VariationSetup (d : VariationData X q) : Prop :=
  0 < d.T ∧ d.T < d.extendedT ∧ FlowStage X d.o d.h d.U d.P d.rho ∧
  ControlledExhaustion X d.o d.u ∧ CotangentImmersion d.G ∧
  CotangentSpanningFields X.manifold ∧ WallProfiles d ∧
  StrictEnvelopeContact d ∧
  (SmoothSpaceTime d.Q (Set.Icc 0 d.extendedT) ∧
    ∃ c, 0 < c ∧ ∀ x t, t ∈ Set.Icc 0 d.extendedT →
      c * (1 + distFrom X.metric.form d.o x ^ 2) ≤ d.Q x t ∧
      c * traceWith (gMat (d.h t) x) (gMat X.metric.form x) ≤
        heatOp d.h (Set.Icc 0 d.extendedT) d.Q x t) ∧
  (∀ j, SmoothSpaceTime (d.rhoTail j) (Set.Icc 0 d.extendedT) ∧
    (∃ C : ℝ, ∀ x t, t ∈ Set.Icc 0 d.extendedT →
      0 ≤ d.rhoTail j x t ∧ d.rhoTail j x t ≤ d.rho x t ∧
      d.rho x t - C ≤ d.rhoTail j x t ∧
      0 ≤ heatOp d.h (Set.Icc 0 d.extendedT) (d.rhoTail j) x t)) ∧
  (∀ K : Set (Pt X), IsCompact K → ∀ ε, 0 < ε → ∀ᶠ j in atTop,
    ∀ x ∈ K, ∀ t ∈ Set.Icc 0 d.extendedT, d.rhoTail j x t ≤ ε) ∧
  StrictMono d.A ∧ Tendsto d.A atTop atTop ∧
  (∀ j, 0 < d.A j ∧ (j + 1 : ℝ) ≤ d.B j ∧ CotangentCompact (boundaryCompact d j) ∧
    ∀ x t, t ∈ Set.Icc 0 d.T → d.A j / 3 < d.u x →
      d.rho x t + (j + 1 : ℝ) ≤ baseCost d j x t)

structure VariationDisc (X : KahlerManifold n) where
  f : ℂ → CotangentPoint X.manifold
  w : ℂ → ℂ
  s : ℝ

def discTime (F : VariationDisc X) (ζ : ℂ) : ℝ := F.s * Real.exp (2 * (F.w ζ).re)

/-- Four actual spatial/clock areas and the logarithmic Fourier seminorm.
`discArea` already uses the paper form convention `i g dz∧dζ̄`
(introduction.tex:239-242), hence no extra base-area factor is needed. -/
def variationEnergy (d : VariationData X q) (j : ℕ) (F : VariationDisc X) : ENNReal :=
  discArea X.metric.form (fun ζ => (F.f ζ).1) + euclideanArea (fun ζ => d.G (F.f ζ)) +
  ENNReal.ofReal (gaussArea d.G F.f) +
  (∫⁻ ζ in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (2 * ‖deriv F.w ζ‖ ^ 2)) +
  scalarDSq (fun θ => Real.log (wallProduct d j (F.f (circlePoint θ))))

/-- Competitors have the source's smooth closed-disc regularity. Initial
radial regularization is a separate obligation, never imposed on a variation. -/
def AdmissibleVariationDisc (d : VariationData X q) (j : ℕ) (F : VariationDisc X) : Prop :=
  CotangentDisc F.f ∧ ContDiffOn ℂ ∞ F.w (Metric.closedBall 0 1) ∧ F.w 0 = 0 ∧
  0 < F.s ∧ F.s < d.T ∧ InCotangentTimeChart d.chart (F.f 0) F.s (centerCylinder d) ∧
  (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, discTime F ζ < d.T) ∧
  (∀ θ, F.f (circlePoint θ) ∈ boundaryRegion d j) ∧ variationEnergy d j F ≠ ⊤

def boundaryCost (d : VariationData X q) (j : ℕ) (F : VariationDisc X) : ℝ :=
  circleAverage (fun θ => let y := F.f (circlePoint θ)
    dualNorm (d.h (discTime F (circlePoint θ))) y.1 y.2 +
      wallCost d j y (discTime F (circlePoint θ)) F.s)

def penalizedFunctional (d : VariationData X q) (j : ℕ) (ε : ℝ) (F : VariationDisc X) : ℝ :=
  boundaryCost d j F + ε * (variationEnergy d j F).toReal - d.test (F.f 0) F.s

/-- EReal infimum, so emptiness cannot silently manufacture the real value zero. -/
def localizedInfimum (d : VariationData X q) (j : ℕ) (ε : ℝ) : EReal :=
  ⨅ (F : VariationDisc X) (_ : AdmissibleVariationDisc d j F),
    (penalizedFunctional d j ε F : EReal)

def MinimizingSequence (d : VariationData X q) (j : ℕ) (ε : ℝ)
    (F : ℕ → VariationDisc X) : Prop :=
  (∀ ν, AdmissibleVariationDisc d j (F ν)) ∧
  Tendsto (fun ν => (penalizedFunctional d j ε (F ν) : EReal)) atTop
    (𝓝 (localizedInfimum d j ε))

/-- The source's initial approximation shrinks both the spatial disc and
clock; it preserves the actual center and physical center time. -/
def radialVariationDisc (F : VariationDisc X) (r : ℝ) : VariationDisc X :=
  { f := fun ζ => F.f ((r : ℂ) * ζ)
    w := fun ζ => F.w ((r : ℂ) * ζ)
    s := F.s }

/-- Extra initial regularity, separate from admissibility. A common radius
works for the initial spatial disc and clock; columns are not constrained. -/
def InitiallyExtendedVariationDisc (F : VariationDisc X) : Prop :=
  ∃ R : ℝ, 1 < R ∧ CotangentDisc (fun ζ => F.f ((R : ℂ) * ζ)) ∧
    ContDiffOn ℂ ∞ (fun ζ => F.w ((R : ℂ) * ζ)) (Metric.closedBall 0 1)

/-- Concrete internal approximation obligation from variation.tex:143–148.
The infimum still ranges over all smooth closed-disc competitors. Initial
radial approximants preserve it and give minimizing sequences to which D05
applies. Energy control keeps any common energy bound after an arbitrarily
small error. This is a target, not an assumed approximation theorem. -/
def InitialDiscRegularization (d : VariationData X q) : Prop :=
  (∀ j ε (F : VariationDisc X), AdmissibleVariationDisc d j F →
    ∀ δ : ℝ, 0 < δ → ∃ r : ℝ, 0 < r ∧ r < 1 ∧
      AdmissibleVariationDisc d j (radialVariationDisc F r) ∧
      InitiallyExtendedVariationDisc (radialVariationDisc F r) ∧
      |(variationEnergy d j (radialVariationDisc F r)).toReal -
        (variationEnergy d j F).toReal| < δ ∧
      |penalizedFunctional d j ε (radialVariationDisc F r) -
        penalizedFunctional d j ε F| < δ) ∧
  (∀ j ε, (⨅ (F : VariationDisc X) (_ : AdmissibleVariationDisc d j F)
      (_ : InitiallyExtendedVariationDisc F),
        (penalizedFunctional d j ε F : EReal)) = localizedInfimum d j ε) ∧
  ∀ j ε (F : ℕ → VariationDisc X), MinimizingSequence d j ε F →
    ∃ r : ℕ → ℝ,
      (∀ ν, 0 < r ν ∧ r ν < 1 ∧
        InitiallyExtendedVariationDisc (radialVariationDisc (F ν) (r ν)) ∧
        |(variationEnergy d j (radialVariationDisc (F ν) (r ν))).toReal -
          (variationEnergy d j (F ν)).toReal| ≤ (ν + 1 : ℝ)⁻¹) ∧
      MinimizingSequence d j ε (fun ν => radialVariationDisc (F ν) (r ν))

/-- Quantified form of `limsup a_ν ≤ 0`; no real limsup junk at an
unbounded sequence is possible. -/
def SeqUpperZero (a : ℕ → ℝ) : Prop :=
  ∀ r, 0 < r → ∀ᶠ ν in atTop, a ν ≤ r

/-- The sequential limit is taken before ε↓0. -/
def EpsSeqZero (a : ℝ → ℕ → ℝ) : Prop :=
  ∀ r, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ∀ᶠ ν in atTop, |a ε ν| ≤ r

/-- The sequential, ε↓0, j→∞ approximation order. -/
def LocalizedZero (a : ℕ → ℝ → ℕ → ℝ) : Prop :=
  ∀ r, 0 < r → ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
    ∀ᶠ ν in atTop, |a j ε ν| ≤ r

def spatialHessian (b : CotangentPoint X.manifold → ℝ) (y : CotangentPoint X.manifold) :
    CotangentMatrix n :=
  leviMatrix (fun z => b (cotangentChartInv y.1 z)) (cotangentChart y.1 y) cotangentDir

def boundaryHessian (d : VariationData X q) (j : ℕ) (F : VariationDisc X) (ζ : ℂ) :
    CotangentMatrix n :=
  spatialHessian (fun y => dualNorm (d.h (discTime F ζ)) y.1 y.2 +
    wallCost d j y (discTime F ζ) F.s) (F.f ζ)

def wallPower (d : VariationData X q) (j a : ℕ) (y : CotangentPoint X.manifold) : ℝ :=
  wallProduct d j y ^ a

def boundarySymbol (d : VariationData X q) (j a : ℕ) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (ζ : ℂ) : CotangentMatrix n :=
  ((wallPower d j a (F.f ζ)) ^ 2 : ℂ) • ((E ζ)ᴴ * boundaryHessian d j F ζ * E ζ)

def outerCenter (d : VariationData X q) (j a : ℕ) (F : VariationDisc X) : ℝ :=
  Real.exp (circleAverage (fun θ => Real.log (wallPower d j a (F.f (circlePoint θ)))))

def centerTestHessian (d : VariationData X q) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) : CotangentMatrix n :=
  (E 0)ᴴ * spatialHessian (fun y => d.test y F.s) (F.f 0) * E 0

def quadValue (A : CotangentMatrix n) (v : CotangentIndex n → ℂ) : ℝ :=
  (star v ⬝ᵥ (A *ᵥ v)).re

def HolomorphicColumn (l : ℂ → CotangentIndex n → ℂ) : Prop :=
  ∀ i, ContDiffOn ℂ ∞ (fun ζ => l ζ i) (Metric.closedBall 0 1)

/-- The ε coefficient is chosen before ε,E₀,D₀,F,E,l. Thus it cannot
depend on interior compacta, Taylor constants, the test or auxiliary loss.
The admissible ε range/margin may depend on the test, as in the source. -/
def DeformationEstimateWith (d : VariationData X q) (j a : ℕ) (L C : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ E₀ D₀ : ℝ,
  ∀ (F : ℕ → VariationDisc X) (E : ℕ → ℂ → CotangentMatrix n)
    (l : ℕ → ℂ → CotangentIndex n → ℂ),
  MinimizingSequence d j ε F →
  (∃ compactCenters : Set (CotangentCoord n × ℝ), IsCompact compactCenters ∧
    compactCenters ⊆ interior (centerCylinder d) ∧ ∀ ν,
      InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s compactCenters) →
  (∀ ν, (variationEnergy d j (F ν)).toReal ≤ E₀ ∧
    NormalizedDiscFrame d.G (F ν).f (E ν) ∧ HolomorphicColumn (l ν) ∧
    (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ν ζ i‖ ^ 2 ≤ L ^ 2) ∧
    boundaryDSq (fun θ => l ν (circlePoint θ)) ≤ ENNReal.ofReal (D₀ ^ 2)) →
  SeqUpperZero (fun ν =>
    outerCenter d j a (F ν) ^ 2 * quadValue (centerTestHessian d (F ν) (E ν)) (l ν 0) -
    circleAverage (fun θ => quadValue (boundarySymbol d j a (F ν) (E ν) (circlePoint θ))
      (l ν (circlePoint θ))) -
    C * ε * (1 + (variationEnergy d j (F ν)).toReal +
      (boundaryDSq (fun θ => l ν (circlePoint θ))).toReal))

/-- The coefficient depends on the cylinder and boundary geometry, but is
chosen before the smooth test as well as before all sequence parameters. -/
def DeformationEstimate (d : VariationData X q) (j a : ℕ) : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 ≤ C ∧
    ∀ φ : CotangentPoint X.manifold → ℝ → ℝ,
      StrictEnvelopeContact {d with test := φ} →
      DeformationEstimateWith {d with test := φ} j a L C


def LocalizedMinimizers (d : VariationData X q)
    (F : ℕ → ℝ → ℕ → VariationDisc X) : Prop :=
  ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F j ε)

/-- Localization, infimum and small-wall conclusions, before any Hessian
test. Each formula keeps the sequence limit inside the ε limit. -/
def LocalizationEstimates (d : VariationData X q) : Prop :=
  Tendsto (fun j => localizedInfimum d j 0) atTop (𝓝 0) ∧
  (∀ᶠ j in atTop,
    (∃ F, AdmissibleVariationDisc d j F) ∧
    localizedInfimum d j 0 ≠ ⊥ ∧ localizedInfimum d j 0 ≠ ⊤ ∧
    MonotoneOn (localizedInfimum d j) (Set.Ici 0) ∧
    Tendsto (localizedInfimum d j) (𝓝[>] (0 : ℝ)) (𝓝 (localizedInfimum d j 0)) ∧
    ∀ ε, 0 < ε → ∀ F, MinimizingSequence d j ε F →
      ∀ r, 0 < r → ∀ᶠ ν in atTop,
        (ε * (variationEnergy d j (F ν)).toReal : EReal) ≤
          localizedInfimum d j ε - localizedInfimum d j 0 + (r : EReal)) ∧
  ∀ F, LocalizedMinimizers d F →
    (∀ᶠ j in atTop, EpsSeqZero (fun ε ν =>
      ε * (1 + (variationEnergy d j (F j ε ν)).toReal))) ∧
    LocalizedZero (fun j ε ν =>
      circleAverage (fun θ => wallCost d j ((F j ε ν).f (circlePoint θ))
        (discTime (F j ε ν) (circlePoint θ)) (F j ε ν).s)) ∧
    LocalizedZero (fun j ε ν =>
      ‖(cotangentChart d.chart ((F j ε ν).f 0), (F j ε ν).s) - d.contact‖) ∧
    (∃ C : ℝ, ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      circleAverage (fun θ => let y := (F j ε ν).f (circlePoint θ)
        dualNorm (d.h (discTime (F j ε ν) (circlePoint θ))) y.1 y.2) ≤ C)

def SymbolBounds (d : VariationData X q) (a : ℕ) : Prop :=
  ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
    AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
    (∀ θ, (boundarySymbol d j a F E (circlePoint θ)).IsHermitian ∧
      rectOpNorm (boundarySymbol d j a F E (circlePoint θ)) ≤ C) ∧
    matrixDSq (fun θ => boundarySymbol d j a F E (circlePoint θ)) ≤
      ENNReal.ofReal C * (1 + variationEnergy d j F)

/-- A jointly holomorphic family in the actual cotangent atlas, smooth up to
the disc circle, with fixed clock. Local charts vary with the product point
`(parameter, disc variable)`. The radius is data of the family, not a purported
uniform constant. Separate holomorphicity alone is not the contract. -/
def HolomorphicDiscFamily (F : VariationDisc X) (fz : ℂ → ℂ → CotangentPoint X.manifold)
    (r : ℝ) : Prop :=
  0 < r ∧ fz 0 = F.f ∧
  CotangentHolomorphicOn (fun p : ℂ × ℂ => fz p.1 p.2)
    (Metric.ball (0 : ℂ) r ×ˢ Metric.closedBall (0 : ℂ) 1)

/-- A parameter slice has closed-disc regularity by restriction of the joint
map. There is no premise or conclusion extending it past the circle. -/
theorem HolomorphicDiscFamily.cotangentDisc {F : VariationDisc X}
    {fz : ℂ → ℂ → CotangentPoint X.manifold} {r : ℝ}
    (hf : HolomorphicDiscFamily F fz r) {z : ℂ} (hz : z ∈ Metric.ball 0 r) :
    CotangentDisc (fz z) :=
  (hf.2.2.comp (contDiff_const.prodMk contDiff_id)
    (fun _ hζ => ⟨hz, hζ⟩)).cotangentDisc

def RealizesFirstField (d : VariationData X q) (j a : ℕ) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (l : ℂ → CotangentIndex n → ℂ)
    (h α : ℂ → ℂ) (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ) : Prop :=
  HolomorphicDiscFamily F fz r ∧
  (∀ z ∈ Metric.ball (0 : ℂ) r,
    AdmissibleVariationDisc d j {F with f := fz z}) ∧
  (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
    fderiv ℂ (fun z => cotangentChart (F.f ζ).1 (fz z ζ)) 0 1 =
      cotangentVectorOfCoords ((α ζ * h ζ) • (E ζ *ᵥ l ζ))) ∧
  ContDiffOn ℂ ∞ h (Metric.closedBall 0 1) ∧ ContDiffOn ℂ ∞ α (Metric.closedBall 0 1) ∧
  (h 0).im = 0 ∧ (h 0).re = outerCenter d j a F ∧
  (∀ θ, ‖h (circlePoint θ)‖ = wallPower d j a (F.f (circlePoint θ))) ∧
  (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ‖α ζ‖ ≤ 1) ∧
  boundaryDSq (fun θ (_ : Unit) => α (circlePoint θ)) ≤ 1

/-- Realization and Taylor constants may depend on the displayed common
interior compact, E₀,D₀,η and the test. This is separate from the coefficient
in DeformationEstimate. The Taylor estimate is for the WHOLE functional. -/
def DeformationRealization (d : VariationData X q) (j a : ℕ) : Prop :=
  ∀ (L E₀ D₀ ε η : ℝ), 0 ≤ L → 0 < ε → 0 < η →
  ∀ (F : ℕ → VariationDisc X) (E : ℕ → ℂ → CotangentMatrix n)
    (l : ℕ → ℂ → CotangentIndex n → ℂ)
    (K' : Set (CotangentPoint X.manifold)) (Kc : Set (CotangentCoord n × ℝ)),
    CotangentCompact K' → IsCompact Kc → Kc ⊆ interior (centerCylinder d) →
    (∀ ν, AdmissibleVariationDisc d j (F ν) ∧
      (variationEnergy d j (F ν)).toReal ≤ E₀ ∧
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, (F ν).f ζ ∈ K') ∧
      InCotangentTimeChart d.chart ((F ν).f 0) (F ν).s Kc ∧
      NormalizedDiscFrame d.G (F ν).f (E ν) ∧ HolomorphicColumn (l ν) ∧
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ν ζ i‖ ^ 2 ≤ L ^ 2) ∧
      boundaryDSq (fun θ => l ν (circlePoint θ)) ≤ ENNReal.ofReal (D₀ ^ 2)) →
    ∃ r C : ℝ, 0 < r ∧ 0 ≤ C ∧
    ∃ (h α : ℕ → ℂ → ℂ) (fz : ℕ → ℂ → ℂ → CotangentPoint X.manifold),
      (∀ ν, RealizesFirstField d j a (F ν) (E ν) (l ν) (h ν) (α ν) (fz ν) r ∧
        (α ν 0).im = 0 ∧ 0 < (α ν 0).re ∧ -Real.log (α ν 0).re ≤ η ∧
        circleAverage (fun θ => 1 - ‖α ν (circlePoint θ)‖ ^ 2) ≤ η) ∧
      ∀ ν (r' : ℝ), 0 < r' → r' < r →
        let cost := fun z => penalizedFunctional d j ε {(F ν) with f := fz ν z}
        let mixed := (wirt (fun z => wirtBar (fun z' => (cost z' : ℂ)) z 1) 0 1).re
        |circleAverage (fun θ => cost ((r' : ℂ) * circlePoint θ)) - cost 0 - r' ^ 2 * mixed| ≤
          C * r' ^ 3

/-- Actual mixed derivative of the computed energy. The same C works for
all realizations, radii, α losses and interior compacta. -/
def ActualEnergyDerivative (d : VariationData X q) (j a : ℕ) : Prop :=
  ∀ L : ℝ, 0 ≤ L → ∃ C : ℝ, 0 ≤ C ∧
  ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n)
    (l : ℂ → CotangentIndex n → ℂ) (h α : ℂ → ℂ)
    (fz : ℂ → ℂ → CotangentPoint X.manifold) (r : ℝ),
    AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
    HolomorphicColumn l →
    (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, ∑ i, ‖l ζ i‖ ^ 2 ≤ L ^ 2) →
    RealizesFirstField d j a F E l h α fz r →
    |(wirt (fun z => wirtBar (fun z' =>
      ((variationEnergy d j {F with f := fz z'}).toReal : ℂ)) z 1) 0 1).re| ≤
      C * (1 + (variationEnergy d j F).toReal +
        (boundaryDSq (fun θ => l (circlePoint θ))).toReal)

/-- V03 covers initial radial regularization (variation.tex:143–148),
localization and the actual boundary-controlled energy derivative, including
the full logarithmic wall energy. Only initial approximants are extended. -/
def V03Contract (X : KahlerManifold n) : Prop :=
  ∀ q (d : VariationData X q), VariationSetup d →
    InitialDiscRegularization d ∧ LocalizationEstimates d ∧
    ∃ a₀ : ℕ, 4 ≤ a₀ ∧ ∀ a, a₀ ≤ a →
      SymbolBounds d a ∧ ∀ j, ActualEnergyDerivative d j a

/-- Spectral scalar calculus is derived from the matrix's eigenvectors and
eigenvalues; the non-Hermitian branch is irrelevant under SymbolBounds. -/
def hermitianScalar (g : ℝ → ℝ) (A : CotangentMatrix n) : CotangentMatrix n :=
  if hA : A.IsHermitian then
    (hA.eigenvectorUnitary : CotangentMatrix n) *
      Matrix.diagonal (fun i => (g (hA.eigenvalues i) : ℂ)) *
        (hA.eigenvectorUnitary : CotangentMatrix n)ᴴ
  else 0

def matrixNegative (A : CotangentMatrix n) : CotangentMatrix n :=
  hermitianScalar (fun x => max (-x) 0) A

def matrixPositive (A : CotangentMatrix n) : CotangentMatrix n :=
  hermitianScalar (fun x => max x 0) A

def smoothMajorant (δ : ℝ) (A : CotangentMatrix n) : CotangentMatrix n :=
  hermitianScalar (fun x => δ + (x + Real.sqrt (x ^ 2 + δ ^ 2)) / 2) A

def negativeTrace (d : VariationData X q) (j a : ℕ) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (power : ℕ) : ℝ :=
  circleAverage (fun θ => (Matrix.trace
    (matrixNegative (boundarySymbol d j a F E (circlePoint θ)) ^ power)).re)

def fejerMean (A : ℝ → CotangentMatrix n) (P : ℕ) (θ : ℝ) : CotangentMatrix n :=
  ∑ k ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    (((1 - |(k : ℝ)| / (P + 1)) : ℂ) *
      Complex.exp ((k : ℂ) * θ * Complex.I)) •
        (fun i j => circleFourier (fun t => A t i j) k)

/-- The frequency-shifted Fejér test is an actual polynomial in ζ, not a
freely supplied holomorphic column. All its exponents are positive. -/
def fejerTestColumn (d : VariationData X q) (j a : ℕ) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (P : ℕ) (i : CotangentIndex n)
    (ζ : ℂ) : CotangentIndex n → ℂ :=
  fun r => ∑ k ∈ Finset.Icc (-(P : ℤ)) (P : ℤ),
    ((1 - |(k : ℝ)| / (P + 1)) : ℂ) *
      circleFourier (fun θ => matrixNegative
        (boundarySymbol d j a F E (circlePoint θ)) r i) k *
          ζ ^ (k + (P : ℤ) + 1).toNat

def negativeFejerError (d : VariationData X q) (j a : ℕ) (F : VariationDisc X)
    (E : ℂ → CotangentMatrix n) (P : ℕ) : ℝ :=
  circleAverage (fun θ => matrixFrobSq
    (fejerMean (fun t => matrixNegative (boundarySymbol d j a F E (circlePoint t))) P θ -
      matrixNegative (boundarySymbol d j a F E (circlePoint θ))))

def FejerEstimates (d : VariationData X q) (a : ℕ) : Prop :=
  ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ F E, AdmissibleVariationDisc d j F →
    NormalizedDiscFrame d.G F.f E → ∀ P : ℕ, 0 < P →
      negativeFejerError d j a F E P ≤ C * (1 + (variationEnergy d j F).toReal) / P ∧
      ∀ i, HolomorphicColumn (fejerTestColumn d j a F E P i) ∧
        fejerTestColumn d j a F E P i 0 = 0 ∧
        (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
          ∑ r, ‖fejerTestColumn d j a F E P i ζ r‖ ^ 2 ≤ C ^ 2) ∧
        boundaryDSq (fun θ => fejerTestColumn d j a F E P i (circlePoint θ)) ≤
          ENNReal.ofReal (C * (P + 1))

/-- Both intermediate-frequency limits are required, and P is independent
of the sequence index ν. -/
def IntermediateFrequency (B : ℝ → ℝ) (P : ℝ → ℕ) : Prop :=
  Tendsto (fun ε => B ε / (P ε : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
  Tendsto (fun ε => ε * (P ε : ℝ)) (𝓝[>] (0 : ℝ)) (𝓝 0)

def FrequencySelection (d : VariationData X q) : Prop :=
  ∀ j (F : ℝ → ℕ → VariationDisc X),
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F ε)) →
    EpsSeqZero (fun ε ν => ε * (1 + (variationEnergy d j (F ε ν)).toReal)) →
    ∃ B : ℝ → ℝ, (∀ ε, 1 ≤ B ε) ∧
      Tendsto (fun ε => ε * B ε) (𝓝[>] (0 : ℝ)) (𝓝 0) ∧
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
        1 + (variationEnergy d j (F ε ν)).toReal ≤ B ε) ∧
      IntermediateFrequency B (fun ε => max 1 (Nat.ceil (Real.sqrt (B ε / ε))))

/-- Symplectic cost on a frame, using its actual canonical bivector.
The antisymmetric-tensor convention contributes the factor one half. -/
def bivectorCost (A J : CotangentMatrix n) : ℝ :=
  (1 / 2 : ℝ) * (∑ i, ∑ j, ∑ k, ∑ l,
    J i j * star (J k l) * A k i * A l j).re

/-- χ and C' are scalar functions, not independently assigned errors. -/
structure ClockData (X : KahlerManifold n) where
  cutoffBaseProfile : ℝ → ℝ
  cutoffFiberProfile : ℝ → ℝ
  fiberCoefficient : ℕ → ℝ
  fiberPower : ℕ
  dampingPower : ℕ
  fiberSupportScale : ℝ

def clockBaseCutoff (d : VariationData X q) (k : ClockData X) (j : ℕ) (x : Pt X) : ℝ :=
  k.cutoffBaseProfile (d.u x / d.A j)

def clockFiberCutoff (d : VariationData X q) (k : ClockData X) (j : ℕ)
    (y : CotangentPoint X.manifold) : ℝ :=
  k.cutoffFiberProfile (dualNorm (d.h 0) y.1 y.2 / d.B j ^ 2)

def clockWeightRaw (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (F : VariationDisc X) (θ : ℝ) : ℝ :=
  let y := F.f (circlePoint θ)
  let t := discTime F (circlePoint θ)
  wallPower d j a y ^ 4 *
    Real.exp (-clockBaseCutoff d k j y.1 *
      (d.rho y.1 t + k.dampingPower * Real.log (j + 3))) *
    Real.exp (-clockFiberCutoff d k j y *
      (Real.log (k.fiberCoefficient j) + k.dampingPower * Real.log (j + 3) +
        k.dampingPower * Real.log (1 + d.B j)))

def clockWeight (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (F : VariationDisc X) (θ : ℝ) : ℝ :=
  clockWeightRaw d k j a F θ / circleAverage (clockWeightRaw d k j a F)

def backwardClock (F : VariationDisc X) (Γ : ℂ → ℂ) (s' : ℝ) : VariationDisc X :=
  {F with s := s', w := fun ζ => F.w ζ + (1 / 2 : ℂ) * Real.log (s' / F.s) * Γ ζ}

def clockBoundaryCost (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (F : VariationDisc X) : ℝ :=
  circleAverage (fun θ => let y := F.f (circlePoint θ)
    let t := discTime F (circlePoint θ)
    t / F.s * clockWeight d k j a F θ *
      (derivWithin (fun t' => dualNorm (d.h t') y.1 y.2) (Set.Ici 0) t +
        derivWithin (fun t' => baseCost d j y.1 t') (Set.Ici 0) t) + wallBase d j y.1 + wallFiber d j y)

def clockSymplecticCost (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (F : VariationDisc X) : ℝ :=
  circleAverage (fun θ => discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
    symplecticP (boundaryHessian d j F (circlePoint θ)))

def ClockCutoffs (d : VariationData X q) (k : ClockData X) : Prop :=
  0 < k.fiberSupportScale ∧ ContDiff ℝ ∞ k.cutoffBaseProfile ∧
  ContDiff ℝ ∞ k.cutoffFiberProfile ∧
  (∀ j, 1 ≤ k.fiberCoefficient j ∧ SmoothFn (clockBaseCutoff d k j) ∧
    (∀ x, 0 ≤ clockBaseCutoff d k j x ∧ clockBaseCutoff d k j x ≤ 1 ∧
      (deltaBase d j x ≠ 1 → clockBaseCutoff d k j x = 1)) ∧
    Function.support (clockBaseCutoff d k j) ⊆ {x | d.A j / 3 < d.u x} ∧
    (∀ y, 0 ≤ clockFiberCutoff d k j y ∧ clockFiberCutoff d k j y ≤ 1 ∧
      (deltaFiber d j y ≠ 1 → clockFiberCutoff d k j y = 1)) ∧
    Function.support (clockFiberCutoff d k j) ⊆
      {y | k.fiberSupportScale * d.B j ^ 2 < dualNorm (d.h 0) y.1 y.2} ∧
    ∀ x, ContDiffOn ℝ ∞ (fun z => clockFiberCutoff d k j (cotangentChartInv x z))
      (cotangentTarget x)) ∧
  Tendsto (fun j => Real.log (k.fiberCoefficient j) / d.B j ^ 2) atTop (𝓝 0)

def spatialBoundaryHessianAt (d : VariationData X q) (j : ℕ)
    (y : CotangentPoint X.manifold) (t s : ℝ) : CotangentMatrix n :=
  spatialHessian (fun y' => dualNorm (d.h t) y'.1 y'.2 + wallCost d j y' t s) y

/-- The same C'_j and fixed power work for EVERY fiber radius b. This
enforces the paper's noncircular choice of C'_j before increasing B_j. -/
def FiberWallError (d : VariationData X q) (k : ClockData X) : Prop :=
  ∀ (j : ℕ) (b : ℝ), (j + 1 : ℝ) ≤ b →
    let db := {d with B := Function.update d.B j b}
    ∀ y ∈ boundaryRegion db j, ∀ t ∈ Set.Icc 0 d.T,
    ∀ s ∈ Set.Icc d.cylinderTimeLo d.cylinderTimeHi,
      |symplecticP (spatialBoundaryHessianAt db j y t s) -
        derivWithin (fun t' => dualNorm (d.h t') y.1 y.2) (Set.Ici 0) t -
        laplacian (d.h t) (fun x => baseCost d j x t + (1 + s) * wallBase d j x) y.1| ≤
      k.fiberCoefficient j * (1 + b) ^ k.fiberPower *
        (wallProduct db j y ^ k.fiberPower)⁻¹ *
          (if clockFiberCutoff db k j y = 1 then 1 else 0)

def BaseWallError (d : VariationData X q) (k : ClockData X) : Prop :=
  ∃ C : ℝ, 0 ≤ C ∧ ∀ j x t, t ∈ Set.Icc 0 d.T → d.u x < d.A j →
    |laplacian (d.h t) (wallBase d j) x| ≤
      C * Real.exp (d.rho x t) * (deltaBase d j x ^ 3)⁻¹ *
        (if clockBaseCutoff d k j x = 1 then 1 else 0)

def ClockLift (d : VariationData X q) (k : ClockData X) (j a : ℕ)
    (F : VariationDisc X) (Γ : ℂ → ℂ) : Prop :=
  ContDiffOn ℂ ∞ Γ (Metric.closedBall 0 1) ∧ Γ 0 = 0 ∧
  ∀ θ, (Γ (circlePoint θ)).re = clockWeight d k j a F θ - 1

def BackwardClockRealization (d : VariationData X q) (k : ClockData X) (j a : ℕ) : Prop :=
  ∀ F, AdmissibleVariationDisc d j F →
    InCotangentTimeChart d.chart (F.f 0) F.s (interior (centerCylinder d)) →
    ∃ Γ, ClockLift d k j a F Γ ∧ ∃ r : ℝ, 0 < r ∧
      ∀ s', 0 < s' → F.s - r < s' → s' < F.s →
        AdmissibleVariationDisc d j (backwardClock F Γ s') ∧
        (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
          discTime (backwardClock F Γ s') ζ ≤ discTime F ζ) ∧
        ∀ θ, discTime (backwardClock F Γ s') (circlePoint θ) =
          discTime F (circlePoint θ) * (s' / F.s) ^ (clockWeight d k j a F θ)

def SpectralFactorFor (d : VariationData X q) (j a : ℕ) (δ : ℝ)
    (F : VariationDisc X) (E H Hinv : ℂ → CotangentMatrix n) : Prop :=
  (∀ i j, ContDiffOn ℂ ∞ (fun ζ => H ζ i j) (Metric.closedBall 0 1) ∧
    ContDiffOn ℂ ∞ (fun ζ => Hinv ζ i j) (Metric.closedBall 0 1)) ∧
  (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, H ζ * Hinv ζ = 1 ∧ Hinv ζ * H ζ = 1) ∧
  ∀ θ, (H (circlePoint θ))ᴴ * H (circlePoint θ) =
    smoothMajorant δ (boundarySymbol d j a F E (circlePoint θ))

/-- The spectral factors have the source's fixed-δ seminorm control and
the inverse sup bound needed for disc-dependent tests. -/
def SpectralFactorEstimates (d : VariationData X q) (a : ℕ) : Prop :=
  ∀ (j : ℕ) (δ : ℝ), 0 < δ → ∃ C : ℝ, 0 ≤ C ∧
    ∀ (F : VariationDisc X) (E : ℂ → CotangentMatrix n),
      AdmissibleVariationDisc d j F →
      NormalizedDiscFrame d.G F.f E →
      ∃ H Hinv : ℂ → CotangentMatrix n,
        SpectralFactorFor d j a δ F E H Hinv ∧
        (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, rectOpNorm (Hinv ζ) ≤ (Real.sqrt δ)⁻¹) ∧
        matrixDSq (fun θ => Hinv (circlePoint θ)) ≤
          ENNReal.ofReal C * (1 + variationEnergy d j F)

/-- Matrix upper violation tested against every unit column, which may
depend on the disc. A fixed eigenvector is never smuggled into the limit. -/
def CenterMajorants (d : VariationData X q) (a : ℕ) : Prop :=
  ∀ᶠ j in atTop, ∀ δ : ℝ, 0 < δ →
  ∀ (F : ℝ → ℕ → VariationDisc X) (E H Hinv : ℝ → ℕ → ℂ → CotangentMatrix n),
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F ε) ∧
      ∀ ν, NormalizedDiscFrame d.G (F ε ν).f (E ε ν) ∧
        SpectralFactorFor d j a δ (F ε ν) (E ε ν) (H ε ν) (Hinv ε ν)) →
    EpsSeqZero (fun ε ν => ε * (1 + (variationEnergy d j (F ε ν)).toReal)) →
    ∀ r : ℝ, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      (((1 + r : ℝ) : ℂ) • ((H ε ν 0)ᴴ * H ε ν 0) -
        ((outerCenter d j a (F ε ν)) ^ 2 : ℂ) •
          centerTestHessian d (F ε ν) (E ε ν)).PosSemidef

def PositiveReplacement (d : VariationData X q) (k : ClockData X) (a : ℕ) : Prop :=
  ∀ j, ∃ C : ℝ, 0 ≤ C ∧ ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
    ∀ (F : ℝ → ℕ → VariationDisc X) (E : ℝ → ℕ → ℂ → CotangentMatrix n),
      (∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F ε) ∧
        ∀ ν, NormalizedDiscFrame d.G (F ε ν).f (E ε ν)) →
      EpsSeqZero (fun ε ν => negativeTrace d j a (F ε ν) (E ε ν) 1) →
      ∀ r, 0 < r → ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
        |clockSymplecticCost d k j a (F ε ν) - circleAverage (fun θ =>
          discTime (F ε ν) (circlePoint θ) / (F ε ν).s *
          clockWeight d k j a (F ε ν) θ *
          (wallPower d j a ((F ε ν).f (circlePoint θ)) ^ 4)⁻¹ *
          bivectorCost (smoothMajorant δ (boundarySymbol d j a (F ε ν) (E ε ν) (circlePoint θ)))
            (frameBivector (E ε ν (circlePoint θ))))| ≤ C * δ + r

def SymplecticSubmean (d : VariationData X q) (k : ClockData X) (a : ℕ) : Prop :=
  ∀ j δ (F : VariationDisc X) (E H Hinv : ℂ → CotangentMatrix n), 0 < δ →
    AdmissibleVariationDisc d j F → NormalizedDiscFrame d.G F.f E →
    SpectralFactorFor d j a δ F E H Hinv →
    Real.exp (circleAverage (fun θ => Real.log (clockWeight d k j a F θ))) *
      (outerCenter d j a F ^ 4)⁻¹ * bivectorCost ((H 0)ᴴ * H 0) (frameBivector (E 0)) ≤
      circleAverage (fun θ => discTime F (circlePoint θ) / F.s * clockWeight d k j a F θ *
        (wallPower d j a (F.f (circlePoint θ)) ^ 4)⁻¹ *
        bivectorCost ((H (circlePoint θ))ᴴ * H (circlePoint θ))
          (frameBivector (E (circlePoint θ))))

def NegativePartEstimates (d : VariationData X q) (a : ℕ) : Prop :=
  ∀ᶠ j in atTop, ∀ (F : ℝ → ℕ → VariationDisc X) (E : ℝ → ℕ → ℂ → CotangentMatrix n),
    (∀ᶠ ε in 𝓝[>] (0 : ℝ), MinimizingSequence d j ε (F ε) ∧
      ∀ ν, NormalizedDiscFrame d.G (F ε ν).f (E ε ν)) →
    EpsSeqZero (fun ε ν => ε * (1 + (variationEnergy d j (F ε ν)).toReal)) →
    EpsSeqZero (fun ε ν => negativeTrace d j a (F ε ν) (E ε ν) 3) ∧
    EpsSeqZero (fun ε ν => negativeTrace d j a (F ε ν) (E ε ν) 1)

def ClockEstimates (d : VariationData X q) (k : ClockData X) (a : ℕ) : Prop :=
  ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀ (F : ℕ → ℝ → ℕ → VariationDisc X), LocalizedMinimizers d F →
    LocalizedZero (fun j ε ν =>
      circleAverage (fun θ => -Real.log (clockWeightRaw d k j a (F j ε ν) θ))) ∧
    LocalizedZero (fun j ε ν =>
      circleAverage (clockWeightRaw d k j a (F j ε ν)) - 1) ∧
    LocalizedZero (fun j ε ν =>
      circleAverage (fun θ => Real.log (clockWeight d k j a (F j ε ν) θ))) ∧
    (∀ r, 0 < r → ∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ᶠ ν in atTop,
      clockSymplecticCost d k j a (F j ε ν) ≤ clockBoundaryCost d k j a (F j ε ν) + r) ∧
    (∀ᶠ j in atTop, ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      SeqUpperZero (fun ν => clockBoundaryCost d k j a (F j ε ν) -
        deriv (d.test ((F j ε ν).f 0)) (F j ε ν).s -
        C j * ε * (1 + (variationEnergy d j (F j ε ν)).toReal)))

/-- V04 chooses the coefficient BEFORE enlarging the fiber walls. All
subsequent estimates refer to that same enlarged localization `db`. This
prevents a circular choice of C'_j depending on B_j. -/
def V04Contract (X : KahlerManifold n) : Prop :=
  ∀ q (d : VariationData X q), VariationSetup d →
    ∃ k : ClockData X, FiberWallError d k ∧ BaseWallError d k ∧
    ∃ B : ℕ → ℝ, (∀ j, d.B j ≤ B j) ∧
      let db := {d with B := B}
      VariationSetup db ∧ ClockCutoffs db k ∧
      ∃ a₀ : ℕ, 4 ≤ a₀ ∧ k.fiberPower + 3 ≤ 4 * a₀ ∧
        k.fiberPower + 3 < k.dampingPower ∧ ∀ a, a₀ ≤ a →
        (∀ᶠ j in atTop, DeformationEstimate db j a) → SymbolBounds db a →
        LocalizationEstimates db →
        FejerEstimates db a ∧ FrequencySelection db ∧ NegativePartEstimates db a ∧
        CenterMajorants db a ∧ SpectralFactorEstimates db a ∧
        ClockEstimates db k a ∧ (∀ᶠ j in atTop, BackwardClockRealization db k j a) ∧
        PositiveReplacement db k a ∧ SymplecticSubmean db k a

/-- V02 includes the actual holomorphic realization and its uniform Taylor
remainder, while selecting the final ε coefficient independently. -/
def V02Contract (X : KahlerManifold n) : Prop :=
  ∀ q (d : VariationData X q), VariationSetup d →
    ∃ a₀ : ℕ, 4 ≤ a₀ ∧ ∀ a, a₀ ≤ a → ∀ᶠ j in atTop,
      DeformationEstimate d j a ∧ DeformationRealization d j a

end Yau.Blueprint
