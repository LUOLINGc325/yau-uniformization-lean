import Yau.Blueprint.Analytic
import spec.CHAIN.HeatConcreteBindings

/-! Exact predicates and partial statement bindings for the four registered mass
producers. Only RVBallBridgeTarget is a complete producer declaration here.
The other declarations deliberately say Fragment: no energy-space realization,
weak solution, kernel or regularity theorem is asserted or presumed. -/
open MeasureTheory Filter
open scoped Topology ContDiff Manifold ENNReal
noncomputable section
namespace Yau.MassTargetStatements
open Yau.Blueprint Yau.HeatConcreteBindings
variable {n : ℕ} {M : ComplexManifold n}

def ballAverage (g : HermitianField M) (μ : Measure M.Carrier)
    (o : M.Carrier) (r : ℝ) (a : M.Carrier → ℝ) : ℝ :=
  (∫ x in distBall g o r, a x ∂μ) / (μ (distBall g o r)).toReal

/-- G02/G03/G04 producer output, before use of the F02 estimate. The chosen
volume is identified with EVERY actual chart-volume witness. Positivity and
finiteness prevent both zero-denominator and infinite-measure cancellation. -/
def RVBallBridgeTarget (X : KahlerManifold n) : Prop :=
  ∃ μg : Measure (Pt X), IsRiemannianVolume X.metric.form μg ∧
    (∀ μ, IsRiemannianVolume X.metric.form μ → μ = μg) ∧
    ∀ (o : Pt X) (r : ℝ), 0 < r →
      MeasurableSet (distBall X.metric.form o r) ∧
      0 < μg (distBall X.metric.form o r) ∧
      μg (distBall X.metric.form o r) < ⊤ ∧
      ∀ (a : Pt X → ℝ) (B : ℝ),
        IntegrableOn a (distBall X.metric.form o r) μg →
        (∀ᵐ x ∂μg.restrict (distBall X.metric.form o r), 0 ≤ a x) → 0 ≤ B →
        (∫⁻ x in distBall X.metric.form o r, ENNReal.ofReal (a x) ∂μg) =
          ENNReal.ofReal (∫ x in distBall X.metric.form o r, a x ∂μg) ∧
        (BallIntegralLE X.metric.form μg o a r B ↔
          ballAverage X.metric.form μg o r a ≤ B)

/-- Same fixed initial volume throughout; this is the actual H=L² pivot,
not an arbitrary Hilbert-space input. -/
abbrev FixedPivot (μg : Measure M.Carrier) (O : Set M.Carrier) :=
  Lp ℝ 2 (μg.restrict O)

def SpatialTest (O : Set M.Carrier) (u : M.Carrier → ℝ) : Prop :=
  SmoothFn u ∧ HasCompactSupport u ∧ tsupport u ⊆ O

def fixedL2Sq (μg : Measure M.Carrier) (O : Set M.Carrier)
    (u : M.Carrier → ℝ) : ℝ := ∫ x in O, |u x| ^ 2 ∂μg

def fixedH1Sq (g : HermitianField M) (μg : Measure M.Carrier)
    (O : Set M.Carrier) (u : M.Carrier → ℝ) : ℝ :=
  ∫ x in O, |u x| ^ 2 + gradNormSq g u x ∂μg

/-- Strong-test restriction of the required intrinsic form. Its actual Δ_ht
and dVg retain the density/drift terms; it is not symmetrized or integrated
against dV_ht. Extending this form to the genuine H¹₀ remains untyped. -/
def intrinsicTestForm (μg : Measure M.Carrier) (O : Set M.Carrier)
    (h : ℝ → HermitianField M) (t : ℝ) (u v : M.Carrier → ℝ) : ℝ :=
  -(∫ x in O, v x * laplacian (h t) u x ∂μg)

/-- Concrete smooth-core portion of INTRINSIC-ENERGY only. All coefficients
and ONE finite L² shift precede time and tests. This is not the full weak
existence/uniqueness target and supplies no presumed extension to H¹₀. -/
def IntrinsicEnergyCoreFragment (X : KahlerManifold n) (h : Flow X) : Prop :=
  ∀ μg, IsRiemannianVolume X.metric.form μg →
    ∀ O : Set (Pt X), SmoothPrecompactDomain O → ∀ T : ℝ, 0 < T →
      ∃ C α shift : ℝ, 0 < C ∧ 0 < α ∧ 0 ≤ shift ∧
        ∀ t ∈ Set.Icc 0 T, ∀ u v : Pt X → ℝ,
          SpatialTest O u → SpatialTest O v →
          MemLp u 2 (μg.restrict O) ∧ MemLp v 2 (μg.restrict O) ∧
          IntegrableOn (fun x => gradNormSq X.metric.form u x) O μg ∧
          IntegrableOn (fun x => v x * laplacian (h t) u x) O μg ∧
          |intrinsicTestForm μg O h t u v| ≤
            C * Real.sqrt (fixedH1Sq X.metric.form μg O u) *
              Real.sqrt (fixedH1Sq X.metric.form μg O v) ∧
          α * fixedH1Sq X.metric.form μg O u ≤
            intrinsicTestForm μg O h t u u + shift * fixedL2Sq μg O u

abbrev EvolvingKernel (M : ComplexManifold n) :=
  M.Carrier → ℝ → M.Carrier → ℝ → ℝ

/-- Source-variable formal adjoint against dV_hs, including +R_hs.
The source time is the fourth argument of the SAME kernel. -/
def sourceAdjoint (h : ℝ → HermitianField M) (G : EvolvingKernel M)
    (x : M.Carrier) (t : ℝ) (y : M.Carrier) (s : ℝ) : ℝ :=
  -derivWithin (fun r => G x t y r) (Set.Icc 0 t) s -
    laplacian (h s) (fun z => G x t z s) y + scalarCurvature (h s) y * G x t y s

/-- dV_hs is chosen at the SOURCE time. The input measure family is constrained
by IsRiemannianVolume in EvolvingKernelPDEFragment; it is never arbitrary. -/
def greenPotential (ν : ℝ → Measure M.Carrier) (O : Set M.Carrier)
    (G : EvolvingKernel M) (f : M.Carrier → ℝ → ℝ) (x : M.Carrier) (t : ℝ) : ℝ :=
  ∫ s in Set.Ioo 0 t, (∫ y in O, G x t y s * f y s ∂ν s)

/-- Partial kernel output: forward/adjoint equations, positive interior,
zero lateral values, and actual source-time delta normalization. Missing
energy representation and nested-domain coherence are NOT hidden premises. -/
def EvolvingKernelPDEFragment (h : ℝ → HermitianField M)
    (ν : ℝ → Measure M.Carrier) (O : Set M.Carrier) (T : ℝ)
    (G : EvolvingKernel M) : Prop :=
  (∀ s ∈ Set.Icc 0 T, IsRiemannianVolume (h s) (ν s)) ∧
  (∀ x ∈ O, ∀ y ∈ O, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T →
    0 < G x t y s ∧
    HasDerivWithinAt (fun r => G x r y s)
      (laplacian (h t) (fun z => G z t y s) x) (Set.Icc s T) t ∧
    HasDerivWithinAt (fun r => G x t y r)
      (-laplacian (h s) (fun z => G x t z s) y + scalarCurvature (h s) y * G x t y s)
      (Set.Icc 0 t) s ∧
    sourceAdjoint h G x t y s = 0) ∧
  (∀ x ∈ frontier O, ∀ y ∈ O, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → G x t y s = 0) ∧
  (∀ y ∈ frontier O, ∀ x ∈ O, ∀ s t : ℝ, 0 ≤ s → s < t → t ≤ T → G x t y s = 0) ∧
  ∀ s ∈ Set.Ico 0 T, ∀ x ∈ O, ∀ φ : M.Carrier → ℝ,
    SpatialTest O φ →
    Tendsto (fun t => ∫ y in O, G x t y s * φ y ∂ν s) (𝓝[>] s) (𝓝 (φ x))

/-- Local smoothness uses actual charts restricted to O. -/
def SmoothSpaceTimeOn (O : Set M.Carrier) (I : Set ℝ)
    (u : M.Carrier → ℝ → ℝ) : Prop :=
  ∀ x : M.Carrier, ContDiffOn ℝ ∞
    (fun p : ComplexVector n × ℝ => u (chartInv x p.1) p.2)
    ((chartTarget x ∩ chartInv x ⁻¹' O) ×ˢ I)

/-- The fixed-source regularity CONCLUSION only, with compact convergence at
zero and no lateral-initial corner jet requirement. Its energy-solution and
particular/homogeneous-remainder antecedents remain genuinely untyped. -/
def FixedSourceConclusionFragment (h : ℝ → HermitianField M)
    (O : Set M.Carrier) (T : ℝ) (f ρ u : M.Carrier → ℝ → ℝ) : Prop :=
  SmoothSpaceTimeOn O (Set.Ioo 0 T) u ∧
  (∀ x ∈ O, ∀ t ∈ Set.Ioo 0 T,
    HasDerivAt (u x) (laplacian (h t) (fun y => u y t) x + f x t) t ∧
    0 ≤ u x t ∧ u x t ≤ ρ x t) ∧
  ∀ K : Set M.Carrier, IsCompact K → K ⊆ O → ∀ ε : ℝ, 0 < ε →
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : ℝ, 0 < t → t < min δ T → ∀ x ∈ K, |u x t| ≤ ε

end Yau.MassTargetStatements
