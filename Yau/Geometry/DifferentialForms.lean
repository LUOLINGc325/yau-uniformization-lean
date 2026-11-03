import Yau.Geometry.Calculus

/-! Real covariant forms and coordinate formulas for P06.  The inputs are actual
continuous alternating multilinear maps on tangent fibers. Coordinate formulas
are total calculators; their tensoriality and reconstruction are obligations,
not facts asserted by this module. The paper convention is G=2 Re h and ω=2 Im h. -/
open scoped Manifold Topology ContDiff ComplexOrder ENNReal
open MeasureTheory
noncomputable section
namespace Yau
variable {n : ℕ} {M : ComplexManifold n}

abbrev RealForm (M : ComplexManifold n) (k : ℕ) :=
  (x : M.Carrier) → (TangentVector M x) [⋀^Fin k]→L[ℝ] ℝ

abbrev FormComponents (n k : ℕ) := ComplexVector n → (Fin k → RIdx n) → ℝ

def formComponents {k : ℕ} (A : RealForm M k) (x : M.Carrier) : FormComponents n k :=
  fun z I => A (chartInv x z) (fun r => chartVec x (chartInv x z) (realVec (I r)))

def SmoothRealForm {k : ℕ} (A : RealForm M k) : Prop :=
  ∀ x I, ContDiffOn ℝ ∞ (fun z => formComponents A x z I) (chartTarget x)

def SmoothFormTime {k : ℕ} (U : ℝ → RealForm M k) (S : Set ℝ) : Prop :=
  ∀ x I, ContDiffOn ℝ ∞
    (fun p : ComplexVector n × ℝ => formComponents (U p.2) x p.1 I)
    (chartTarget x ×ˢ S)

/-- Covariant derivative of every slot, with the real Levi-Civita symbols. -/
def covariantComponents {k : ℕ} (g : HermitianField M) (x : M.Carrier)
    (A : FormComponents n k) (z : ComplexVector n) (a : RIdx n) (I : Fin k → RIdx n) : ℝ :=
  rDeriv (fun w => A w I) z a -
    ∑ r, ∑ c, christoffel g x z c a (I r) * A z (Function.update I r c)

/-- Exterior derivative: omission by `succAbove` fixes the sign convention. -/
def exteriorComponents {k : ℕ} (A : FormComponents n k) : FormComponents n (k + 1) :=
  fun z I => ∑ r : Fin (k + 1), (-1 : ℝ) ^ r.val *
    rDeriv (fun w => A w (fun s => I (r.succAbove s))) z (I r)

/-- Codifferential on degree `k+1`: minus the metric contraction of ∇. -/
def codifferentialComponents {k : ℕ} (g : HermitianField M) (x : M.Carrier)
    (A : FormComponents n (k + 1)) : FormComponents n k :=
  fun z I => -∑ a, ∑ b, (realMetricFn g x z)⁻¹ a b *
    covariantComponents g x A z a (Fin.cons b I)

/-- Nonnegative Hodge Laplacian dδ+δd; δ on degree zero is zero. -/
def hodgeComponents (g : HermitianField M) (x : M.Carrier) :
    (k : ℕ) → FormComponents n k → FormComponents n k
  | 0, A => codifferentialComponents g x (exteriorComponents A)
  | k + 1, A => fun z I =>
      exteriorComponents (codifferentialComponents g x A) z I +
        codifferentialComponents g x (exteriorComponents A) z I

/-- Paper generator -□/2 for G=2 Re h and Δ=tr Levi.
The scalar and closed-form Kähler identities remain unproved bridge targets. -/
def hodgeGeneratorComponents {k : ℕ} (g : HermitianField M) (x : M.Carrier)
    (A : FormComponents n k) : FormComponents n k :=
  fun z I => -(hodgeComponents g x k A z I) / 2

/-- Actual reconstruction condition, tested on the full target of every chart. -/
def RepresentsExterior {k : ℕ} (A : RealForm M k) (B : RealForm M (k + 1)) : Prop :=
  ∀ x z, z ∈ chartTarget x → ∀ I,
    formComponents B x z I = exteriorComponents (formComponents A x) z I

def RepresentsCodifferential {k : ℕ} (g : HermitianField M)
    (A : RealForm M (k + 1)) (B : RealForm M k) : Prop :=
  ∀ x z, z ∈ chartTarget x → ∀ I,
    formComponents B x z I = codifferentialComponents g x (formComponents A x) z I

def RepresentsHodge {k : ℕ} (g : HermitianField M) (A B : RealForm M k) : Prop :=
  ∀ x z, z ∈ chartTarget x → ∀ I,
    formComponents B x z I = hodgeComponents g x k (formComponents A x) z I

def ClosedRealForm {k : ℕ} (A : RealForm M k) : Prop :=
  ∀ x z, z ∈ chartTarget x → ∀ I, exteriorComponents (formComponents A x) z I = 0

/-- The 1/k! inner product on covariant alternating tensors. -/
def formInner {k : ℕ} (g : HermitianField M) (A B : RealForm M k) (x : M.Carrier) : ℝ :=
  (Nat.factorial k : ℝ)⁻¹ * ∑ I : Fin k → RIdx n, ∑ J : Fin k → RIdx n,
    formComponents A x (chartPt x x) I * formComponents B x (chartPt x x) J *
      ∏ r, (realMetricFn g x (chartPt x x))⁻¹ (I r) (J r)

def formNormSq {k : ℕ} (g : HermitianField M) (A : RealForm M k) (x : M.Carrier) : ℝ :=
  formInner g A A x

/-- J-invariance characterizes real (1,1) forms. -/
def RealOneOne (A : RealForm M 2) : Prop :=
  ∀ x u v, A x ![Complex.I • u, Complex.I • v] = A x ![u, v]

/-- Recover h_A(u,v)=(A(u,Jv)+i A(u,v))/2; thus iota(h_A)=A for real (1,1)
forms, pending the representation bridge. No positivity is required of A. -/
def formHermitianMatrix (A : RealForm M 2) (x : M.Carrier) : Matrix (Fin n) (Fin n) ℂ :=
  fun a b =>
    ((A x ![chartVec x x (stdVec a), Complex.I • chartVec x x (stdVec b)] : ℂ) +
      Complex.I * (A x ![chartVec x x (stdVec a), chartVec x x (stdVec b)] : ℂ)) / 2

def formTrace (g : HermitianField M) (A : RealForm M 2) (x : M.Carrier) : ℝ :=
  traceWith (gMat g x) (formHermitianMatrix A x)

/-- Form iota convention ι_F(A)=2 Im A, on arbitrary real chart vectors.
This differs from the symmetric real-matrix representation Parabolic.iota. -/
def RepresentsIota (A : M.Carrier → Matrix (Fin n) (Fin n) ℂ)
    (α : RealForm M 2) : Prop :=
  ∀ x u v, α x ![chartVec x x u, chartVec x x v] =
    2 * (∑ a, ∑ b, star (u a) * A x a b * v b).im

/-- Paper boundedness ±Cg, allowing signed Hermitian forms. -/
def FormOrderBound (g : HermitianField M) (C : ℝ) (A : RealForm M 2) : Prop :=
  ∀ x, (formHermitianMatrix A x - (-C : ℂ) • gMat g x).PosSemidef ∧
    ((C : ℂ) • gMat g x - formHermitianMatrix A x).PosSemidef

def FormLE (A B : RealForm M 2) : Prop :=
  ∀ x, (formHermitianMatrix B x - formHermitianMatrix A x).PosSemidef

/-! ## Concrete prequotient L²/form-domain relations

These relations use the existing Riemannian volume supplied with its exact
`IsRiemannianVolume` law. Completion and descent to an AE quotient are not
performed by this file. In degree two the weak d/δ data have degrees three/one.
-/

def L2RealForm {k : ℕ} (g : HermitianField M) (μ : Measure M.Carrier)
    (A : RealForm M k) : Prop :=
  (∀ x (I : Fin k → RIdx n), AEStronglyMeasurable
    (fun y => A y (fun r => chartVec x y (realVec (I r))))
    (μ.restrict (chartAt (ComplexVector n) x).source)) ∧
  (∫⁻ x, ENNReal.ofReal (formNormSq g A x) ∂μ) < ⊤

def formL2DistanceSq {k : ℕ} (g : HermitianField M) (μ : Measure M.Carrier)
    (A B : RealForm M k) : ℝ≥0∞ :=
  ∫⁻ x, ENNReal.ofReal (formNormSq g (A - B) x) ∂μ

def CompactlySupportedRealForm {k : ℕ} (A : RealForm M k) : Prop :=
  IsCompact (closure {x | A x ≠ 0})

/-- The closure of the Cc∞ d/δ graph in the sum of three L² norms.
This explicitly includes the derivative terms of the q+L² topology. -/
def HodgeFormGraphClosure (g : HermitianField M) (μ : Measure M.Carrier)
    (A : RealForm M 2) (dA : RealForm M 3) (deltaA : RealForm M 1) : Prop :=
  L2RealForm g μ A ∧ L2RealForm g μ dA ∧ L2RealForm g μ deltaA ∧
  ∃ (As : ℕ → RealForm M 2) (ds : ℕ → RealForm M 3) (deltas : ℕ → RealForm M 1),
    (∀ j, SmoothRealForm (As j) ∧ CompactlySupportedRealForm (As j) ∧
      SmoothRealForm (ds j) ∧ RepresentsExterior (As j) (ds j) ∧
      SmoothRealForm (deltas j) ∧ RepresentsCodifferential g (As j) (deltas j) ∧
      L2RealForm g μ (As j) ∧ L2RealForm g μ (ds j) ∧ L2RealForm g μ (deltas j)) ∧
    Filter.Tendsto (fun j => formL2DistanceSq g μ (As j) A +
      formL2DistanceSq g μ (ds j) dA + formL2DistanceSq g μ (deltas j) deltaA)
      Filter.atTop (nhds 0)

/-- Before quotienting: W represents the Friedrichs operator applied to A.
Uniqueness is only up to μ-a.e. equality; it is a separate theorem target. -/
def FriedrichsHodgeRelation (g : HermitianField M) (μ : Measure M.Carrier)
    (A W : RealForm M 2) : Prop :=
  L2RealForm g μ W ∧ ∃ dA deltaA, HodgeFormGraphClosure g μ A dA deltaA ∧
    ∀ V dV deltaV, HodgeFormGraphClosure g μ V dV deltaV →
      Integrable (formInner g dA dV) μ ∧ Integrable (formInner g deltaA deltaV) μ ∧
      Integrable (formInner g W V) μ ∧
      (∫ x, formInner g dA dV x ∂μ) + (∫ x, formInner g deltaA deltaV x ∂μ) =
        ∫ x, formInner g W V x ∂μ

end Yau
