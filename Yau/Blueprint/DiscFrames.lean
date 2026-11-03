import Yau.Blueprint.Nodes

/-!
Concrete induced-coordinate calculus on `Y = T^{*(1,0)}M`.

There is deliberately no user-supplied Gauss map, differential, area, or
bivector. All are calculated from an actual cotangent point and an immersion.
`CotangentPoint` is a point representation, not a claimed product-manifold
trivialization. Smoothness, holomorphicity and compactness below use the
induced cotangent charts, including their transition functions.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section
namespace Yau.Blueprint
open Yau

variable {n q : ℕ} {M : ComplexManifold n}

abbrev CotangentPoint (M : ComplexManifold n) := M.Carrier × Covector n
abbrev CotangentCoord (n : ℕ) := ComplexVector n × ComplexVector n
abbrev CotangentIndex (n : ℕ) := Fin n ⊕ Fin n
abbrev CotangentMatrix (n : ℕ) := Matrix (CotangentIndex n) (CotangentIndex n) ℂ

def cotangentChart (x : M.Carrier) (y : CotangentPoint M) : CotangentCoord n :=
  (chartPt x y.1, covectorCoords x y.1 y.2)

def cotangentChartInv (x : M.Carrier) (z : CotangentCoord n) : CotangentPoint M :=
  (chartInv x z.1, covectorOfCoords x (chartInv x z.1) z.2)

def cotangentTarget (x : M.Carrier) : Set (CotangentCoord n) :=
  chartTarget x ×ˢ Set.univ

/-- The actual domain of an induced cotangent chart. A total chart value
alone never certifies that a point belongs to this domain. -/
def cotangentSource (x : M.Carrier) : Set (CotangentPoint M) :=
  {y | y.1 ∈ (extChartAt (ComplexModel n) x).source}

def InCotangentChart (x : M.Carrier) (y : CotangentPoint M)
    (K : Set (CotangentCoord n)) : Prop :=
  y ∈ cotangentSource x ∧ cotangentChart x y ∈ K

def InCotangentTimeChart (x : M.Carrier) (y : CotangentPoint M) (t : ℝ)
    (K : Set (CotangentCoord n × ℝ)) : Prop :=
  y ∈ cotangentSource x ∧ (cotangentChart x y, t) ∈ K

/-- Holomorphicity into the actual induced cotangent atlas, including complex
smoothness up to the boundary of `S`. The parameter space may be a product.
The base map is manifold-holomorphic; around each parameter point the full
coordinates are checked on a neighborhood whose image lies in the chart
source. The neighborhood and chart may vary, with no global chart restriction. -/
def CotangentHolomorphicOn {P : Type*} [NormedAddCommGroup P] [NormedSpace ℂ P]
    (f : P → CotangentPoint M) (S : Set P) : Prop :=
  ContMDiffOn 𝓘(ℂ, P) (ComplexModel n) ∞ (fun z => (f z).1) S ∧
  ∀ z₀ ∈ S, ∃ V : Set P, IsOpen V ∧ z₀ ∈ V ∧
    (∀ z ∈ S ∩ V, f z ∈ cotangentSource (f z₀).1) ∧
    ContDiffOn ℂ ∞ (fun z => cotangentChart (f z₀).1 (f z)) (S ∩ V)

/-- Restrict a genuine local family along a smooth parameter map. In
particular, a parameter slice of a joint family retains valid local charts. -/
theorem CotangentHolomorphicOn.comp {P Q : Type*}
    [NormedAddCommGroup P] [NormedSpace ℂ P]
    [NormedAddCommGroup Q] [NormedSpace ℂ Q]
    {f : P → CotangentPoint M} {S : Set P} (hf : CotangentHolomorphicOn f S)
    {g : Q → P} (hg : ContDiff ℂ ∞ g) {T : Set Q} (hmap : Set.MapsTo g T S) :
    CotangentHolomorphicOn (fun z => f (g z)) T := by
  refine ⟨hf.1.comp hg.contMDiff.contMDiffOn hmap, fun z₀ hz₀ => ?_⟩
  obtain ⟨V, ho, hv, hs, hd⟩ := hf.2 (g z₀) (hmap hz₀)
  refine ⟨g ⁻¹' V, ho.preimage hg.continuous, hv, ?_, ?_⟩
  · exact fun z hz => hs (g z) ⟨hmap hz.1, hz.2⟩
  · exact hd.comp hg.contDiffOn (fun z hz => ⟨hmap hz.1, hz.2⟩)

def cotangentCoordsVector (z : CotangentCoord n) : CotangentIndex n → ℂ :=
  Sum.elim (WithLp.ofLp z.1) (WithLp.ofLp z.2)

def cotangentVectorOfCoords (v : CotangentIndex n → ℂ) : CotangentCoord n :=
  (WithLp.toLp 2 (fun i => v (.inl i)), WithLp.toLp 2 (fun i => v (.inr i)))

def cotangentTransition (x x' : M.Carrier) (y : CotangentPoint M) : CotangentMatrix n :=
  fun i j => cotangentCoordsVector
    (fderiv ℂ (fun z => cotangentChart x' (cotangentChartInv x z))
      (cotangentChart x y) (cotangentDir j)) i

/-- Compactness in the induced atlas, without imposing a product topology on `Y`. -/
def CotangentCompact (K : Set (CotangentPoint M)) : Prop :=
  ∃ (r : ℕ) (x : Fin r → M.Carrier) (C : Fin r → Set (CotangentCoord n)),
    (∀ i, IsCompact (C i) ∧ C i ⊆ cotangentTarget (x i)) ∧
    K = ⋃ i, cotangentChartInv (x i) '' C i

def CotangentHolomorphic (G : CotangentPoint M → ComplexVector q) : Prop :=
  ∀ x, DifferentiableOn ℂ (fun z => G (cotangentChartInv x z)) (cotangentTarget x)

/-- The differential of the same `G` used in the area and frame definitions. -/
def cotangentDG (G : CotangentPoint M → ComplexVector q) (x : M.Carrier)
    (y : CotangentPoint M) : Matrix (Fin q) (CotangentIndex n) ℂ :=
  fun a b => (fderiv ℂ (fun z => G (cotangentChartInv x z))
    (cotangentChart x y) (cotangentDir b)) a

def CotangentImmersion (G : CotangentPoint M → ComplexVector q) : Prop :=
  CotangentHolomorphic G ∧ Function.Injective G ∧
    ∀ y, Function.Injective (fderiv ℂ (fun z => G (cotangentChartInv y.1 z))
      (cotangentChart y.1 y))

/-- Global holomorphic tangent fields on the actual cotangent bundle,
represented in centered induced charts and checked in every fixed chart. -/
def CotangentSpanningFields (M : ComplexManifold n) : Prop :=
  ∃ (b : ℕ) (Z : Fin b → CotangentPoint M → CotangentIndex n → ℂ),
    (∀ i x k, DifferentiableOn ℂ
      (fun z => (cotangentTransition (chartInv x z.1) x (cotangentChartInv x z) *ᵥ
        Z i (cotangentChartInv x z)) k) (cotangentTarget x)) ∧
    ∀ y, Submodule.span ℂ (Set.range (fun i => Z i y)) = ⊤

def CotangentDisc (f : ℂ → CotangentPoint M) : Prop :=
  IsCotangentDisc (fun ζ => (f ζ).1) (fun ζ => (f ζ).2)

/-- Joint local regularity on the closed disc supplies the ordinary disc
predicate. This restriction does not assert continuation across the circle. -/
theorem CotangentHolomorphicOn.cotangentDisc {f : ℂ → CotangentPoint M}
    (hf : CotangentHolomorphicOn f (Metric.closedBall (0 : ℂ) 1)) :
    CotangentDisc f := by
  refine ⟨hf.1, fun ζ hζ => ?_⟩
  obtain ⟨V, ho, hv, _, hd⟩ := hf.2 ζ hζ
  exact (contDiffWithinAt_inter (ho.mem_nhds hv)).mp ((hd ζ ⟨hζ, hv⟩).snd)

/-- Extra regularity used only for selecting an initial frame in D05.
It is not the class of admissible competitors or deformed slices. -/
def ExtendedCotangentDisc (f : ℂ → CotangentPoint M) : Prop :=
  ∃ r : ℝ, 1 < r ∧ CotangentDisc (fun ζ => f ((r : ℂ) * ζ))

/-- Matrix `E` is a frame along a genuine holomorphic disc. Near every disc
point its coordinates are checked in a valid fixed induced chart. -/
def IsDiscFrame (f : ℂ → CotangentPoint M) (E : ℂ → CotangentMatrix n) : Prop :=
  (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, (E ζ).det ≠ 0) ∧
  CotangentDisc f ∧
  ∀ ζ₀ ∈ Metric.closedBall (0 : ℂ) 1, ∃ V : Set ℂ, IsOpen V ∧ ζ₀ ∈ V ∧
    (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1 ∩ V, f ζ ∈ cotangentSource (f ζ₀).1) ∧
    ∀ i j, ContDiffOn ℂ ∞
      (fun ζ => (cotangentTransition (f ζ).1 (f ζ₀).1 (f ζ) * E ζ) i j)
      (Metric.closedBall 0 1 ∩ V)

def frameInChart (x : M.Carrier) (f : ℂ → CotangentPoint M)
    (E : ℂ → CotangentMatrix n) (ζ : ℂ) : CotangentMatrix n :=
  cotangentTransition (f ζ).1 x (f ζ) * E ζ

def ambientFrame (G : CotangentPoint M → ComplexVector q) (f : ℂ → CotangentPoint M)
    (E : ℂ → CotangentMatrix n) (ζ : ℂ) : Matrix (Fin q) (CotangentIndex n) ℂ :=
  cotangentDG G (f ζ).1 (f ζ) * E ζ

def circlePoint (θ : ℝ) : ℂ := Complex.exp (θ * Complex.I)

/-- Fourier coefficients with normalized circle measure. -/
def circleFourier (a : ℝ → ℂ) (k : ℤ) : ℂ :=
  (2 * Real.pi : ℂ)⁻¹ * ∫ θ in (0 : ℝ)..(2 * Real.pi),
    Complex.exp (-(k : ℂ) * θ * Complex.I) * a θ

/-- The exact Fourier seminorm, as an extended nonnegative real: infinite
energy cannot silently become zero through `ENNReal.toReal`. -/
def boundaryDSq {ι : Type*} [Fintype ι] (a : ℝ → ι → ℂ) : ENNReal :=
  ∑ i, ∑' k : ℤ, ENNReal.ofReal (|k| * ‖circleFourier (fun θ => a θ i) k‖ ^ 2)

def matrixDSq {ι κ : Type*} [Fintype ι] [Fintype κ]
    (a : ℝ → Matrix ι κ ℂ) : ENNReal :=
  boundaryDSq (fun θ (i : ι × κ) => a θ i.1 i.2)

def scalarDSq (a : ℝ → ℝ) : ENNReal :=
  boundaryDSq (fun θ (_ : Unit) => (a θ : ℂ))

def euclideanArea {r : ℕ} (F : ℂ → ComplexVector r) : ENNReal :=
  ∫⁻ ζ in Metric.ball (0 : ℂ) 1, ENNReal.ofReal (2 * ‖fderiv ℂ F ζ 1‖ ^ 2)

/-- Local Plücker potential `log det(V*V)` of the actual Gauss plane. -/
def gaussPotential (G : CotangentPoint M → ComplexVector q) (x : M.Carrier)
    (z : CotangentCoord n) : ℝ :=
  let V := cotangentDG G x (cotangentChartInv x z)
  Real.log (Vᴴ * V).det.re

/-- `∫ (g∘f)* i∂∂̄ log det(V*V)`; the factor 2 is the real-area
conversion `i dζ∧dζ̄ = 2 dA`. No arbitrary Gauss-area input occurs. -/
def gaussArea (G : CotangentPoint M → ComplexVector q) (f : ℂ → CotangentPoint M) : ℝ :=
  ∫ ζ in Metric.ball (0 : ℂ) 1,
    let x := (f ζ).1
    let v := fderiv ℂ (fun η => cotangentChart x (f η)) ζ 1
    2 * (wirt (fun z => wirtBar (fun z' => (gaussPotential G x z' : ℂ)) z v)
      (cotangentChart x (f ζ)) v).re

/-- Components of `Σ e_i∧f_i`, as an antisymmetric tensor. -/
def canonicalBivector : CotangentMatrix n :=
  fun i j => match i, j with
    | .inl a, .inr b => if a = b then 1 else 0
    | .inr a, .inl b => if a = b then -1 else 0
    | _, _ => 0

def frameBivector (E : CotangentMatrix n) : CotangentMatrix n :=
  E⁻¹ * canonicalBivector * E⁻¹ᵀ

def matrixFrobSq {ι κ : Type*} [Fintype ι] [Fintype κ] (A : Matrix ι κ ℂ) : ℝ :=
  ∑ i, ∑ j, ‖A i j‖ ^ 2

def rectOpNorm {ι κ : Type*} [Fintype ι] [Fintype κ]
    (A : Matrix ι κ ℂ) : ℝ := by
  classical
  exact ‖(Matrix.toEuclideanLin A).toContinuousLinearMap‖

def NormalizedDiscFrame (G : CotangentPoint M → ComplexVector q)
    (f : ℂ → CotangentPoint M) (E : ℂ → CotangentMatrix n) : Prop :=
  IsDiscFrame f E ∧
  (∀ θ, (ambientFrame G f E (circlePoint θ))ᴴ * ambientFrame G f E (circlePoint θ) = 1) ∧
  (∀ ζ ∈ Metric.ball (0 : ℂ) 1, rectOpNorm (ambientFrame G f E ζ) ≤ 1) ∧
  matrixDSq (fun θ => ambientFrame G f E (circlePoint θ)) =
    ENNReal.ofReal (gaussArea G f / (2 * Real.pi))

/-- D05 selects frames for the initially extended discs of discs.tex:498.
Its boundary/center estimates apply to any normalized smooth closed-disc
frame: the proof at 678–703 uses only that regularity and normalization.
Neither estimate asks that its disc or frame extend across the circle.
This is a planning obligation, not an assumed or proved theorem. -/
def DiscFramesContract (M : ComplexManifold n) : Prop :=
  ∀ (q : ℕ) (G : CotangentPoint M → ComplexVector q), CotangentImmersion G →
  ∃ chooseE : (ℂ → CotangentPoint M) → ℂ → CotangentMatrix n,
    (∀ f, ExtendedCotangentDisc f → NormalizedDiscFrame G f (chooseE f)) ∧
    (∀ K, CotangentCompact K → ∃ C : ℝ, 0 < C ∧ ∀ f E,
      NormalizedDiscFrame G f E → (∀ θ, f (circlePoint θ) ∈ K) →
      ∀ ζ ∈ Metric.closedBall (0 : ℂ) 1,
        matrixFrobSq (frameBivector (E ζ)) ≤ C ^ 2) ∧
    ∀ K, CotangentCompact K → ∀ (x : M.Carrier) (K₀ : Set (CotangentCoord n)),
      IsCompact K₀ → K₀ ⊆ cotangentTarget x → ∃ C : ℝ, 0 < C ∧ ∀ f E,
      NormalizedDiscFrame G f E → (∀ θ, f (circlePoint θ) ∈ K) →
      InCotangentChart x (f 0) K₀ →
      rectOpNorm (frameInChart x f E 0) ≤ C ∧
      rectOpNorm ((frameInChart x f E 0)⁻¹) ≤ C

end Yau.Blueprint
