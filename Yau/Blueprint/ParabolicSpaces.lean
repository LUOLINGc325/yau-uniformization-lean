import Yau.Geometry.Calculus

/-! Concrete coordinate spaces for the scheduled parabolic leaves. These are
function-space definitions, not asserted analytic estimates. Spatial dimension
is `2*n`; time derivatives at the end faces are taken within the stated slab. -/
open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Parabolic

abbrev Space (n : ℕ) := Yau.ComplexVector n
abbrev Point (n : ℕ) := Space n × ℝ
abbrev Mat (n : ℕ) := Matrix (Yau.RIdx n) (Yau.RIdx n) ℝ
abbrev Sym (n : ℕ) := selfAdjoint (Mat n)

def sym (A : Mat n) : Sym n := selfAdjointPart ℝ A

def cylinder (O : Set (Space n)) (a b : ℝ) : Set (Point n) := O ×ˢ Set.Icc a b

def backward (r : ℝ) : Set (Point n) := Metric.ball 0 r ×ˢ Set.Ioc (-(r^2)) 0

def parabolicDistance (p q : Point n) : ℝ := ‖p.1-q.1‖ + Real.sqrt |p.2-q.2|

def holderWeight (α : ℝ) (p q : Point n) : ℝ :=
  ‖p.1-q.1‖ ^ α + |p.2-q.2| ^ (α/2)

/-- A norm bound is expressed by inequalities, so an unbounded function cannot
obtain norm zero from an unchecked real `sSup`. -/
def HolderBound {V : Type*} [NormedAddCommGroup V]
    (α : ℝ) (Q : Set (Point n)) (f : Point n → V) (C : ℝ) : Prop :=
  0 ≤ C ∧ (∀ p ∈ Q, ‖f p‖ ≤ C) ∧
    ∀ p ∈ Q, ∀ q ∈ Q, ‖f p - f q‖ ≤ C * holderWeight α p q

def spatialD (u : Point n → ℝ) (p : Point n) : Space n →L[ℝ] ℝ :=
  fderiv ℝ (fun x => u (x,p.2)) p.1

def spatialDD (u : Point n → ℝ) (p : Point n) :
    Space n →L[ℝ] Space n →L[ℝ] ℝ :=
  fderiv ℝ (fun x => fderiv ℝ (fun y => u (y,p.2)) x) p.1

def hessian (u : Point n → ℝ) (p : Point n) : Sym n :=
  sym (fun i j => spatialDD u p (Yau.realVec i) (Yau.realVec j))

def timeD (Q : Set (Point n)) (u : Point n → ℝ) (p : Point n) : ℝ :=
  derivWithin (fun t => u (p.1,t)) {t | (p.1,t) ∈ Q} p.2

/-- Parabolic C² means continuous u, D_x u, D²_x u and u_t with
actual spatial and one-sided temporal differentiability. Joint C² in (x,t)
is deliberately not required. -/
def C2 (Q : Set (Point n)) (u : Point n → ℝ) : Prop :=
  ContinuousOn u Q ∧ ContinuousOn (spatialD u) Q ∧
  ContinuousOn (spatialDD u) Q ∧ ContinuousOn (timeD Q u) Q ∧
  (∀ p ∈ Q, ContDiffAt ℝ 2 (fun x => u (x,p.2)) p.1) ∧
  ∀ p ∈ Q, DifferentiableWithinAt ℝ (fun t => u (p.1,t)) {t | (p.1,t) ∈ Q} p.2

/-- Explicit C^(2+α,1+α/2) bound (an equivalent maximum convention).
Only the highest parabolic derivatives have Hölder seminorms. -/
def SchauderBound (α : ℝ) (Q : Set (Point n)) (u : Point n → ℝ) (C : ℝ) : Prop :=
  C2 Q u ∧ 0 ≤ C ∧ (∀ p ∈ Q, |u p| ≤ C ∧ ‖spatialD u p‖ ≤ C) ∧
    HolderBound α Q (spatialDD u) C ∧ HolderBound α Q (timeD Q u) C

def smooth (Q : Set (Point n)) (u : Point n → ℝ) : Prop := ContDiffOn ℝ ∞ u Q

def d (f : Space n → ℝ) (x : Space n) (i : Yau.RIdx n) : ℝ :=
  fderiv ℝ f x (Yau.realVec i)

/-- ∂t-a^(ij)∂ij-b^i∂i. No input field supplies a differential operator. -/
def linearOp (Q : Set (Point n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (u : Point n → ℝ) (p : Point n) : ℝ :=
  timeD Q u p - (∑ i, ∑ j, a p i j * spatialDD u p (Yau.realVec i) (Yau.realVec j)) -
    ∑ i, b p i * spatialD u p (Yau.realVec i)

def Elliptic (Q : Set (Point n)) (a : Point n → Mat n) (lam upper : ℝ) : Prop :=
  0 < lam ∧ lam ≤ upper ∧ ∀ p ∈ Q, (a p).IsSymm ∧
    ∀ v : Yau.RIdx n → ℝ,
      lam * (∑ i, (v i)^2) ≤ ∑ i, ∑ j, a p i j * v i * v j ∧
      (∑ i, ∑ j, a p i j * v i * v j) ≤ upper * (∑ i, (v i)^2)

/-- Smooth bounded domain, using actual smooth defining functions with nonzero
differential at the boundary; no abstract boundary-regularity premise. -/
def SmoothDomain (O : Set (Space n)) : Prop :=
  IsOpen O ∧ O.Nonempty ∧ IsCompact (closure O) ∧
    ∀ x ∈ frontier O, ∃ (V : Set (Space n)) (ρ : Space n → ℝ),
      IsOpen V ∧ x ∈ V ∧ ContDiffOn ℝ ∞ ρ V ∧ ρ x = 0 ∧ fderiv ℝ ρ x ≠ 0 ∧
        O ∩ V = {y | y ∈ V ∧ ρ y < 0}

def Test (Q : Set (Point n)) (φ : Point n → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HasCompactSupport φ ∧ tsupport φ ⊆ Q

def productVolume (O : Set (Space n)) (I : Set ℝ) : Measure (Point n) :=
  (volume.restrict O).prod (volume.restrict I)

/-- Weak spatial derivative, tested against smooth compactly supported functions. -/
def WeakGradient (O : Set (Space n)) (I : Set ℝ) (u : Point n → ℝ)
    (G : Point n → Yau.RIdx n → ℝ) : Prop :=
  ∀ φ : Point n → ℝ, Test (O ×ˢ I) φ → ∀ i,
    (∫ p, u p * d (fun x => φ (x,p.2)) p.1 i ∂productVolume O I) =
      -(∫ p, G p i * φ p ∂productVolume O I)

/-- H¹₀ closure in its actual L² graph norm, including approximating gradients.
The weak-gradient identity is also required, independently of representatives. -/
def H10 (O : Set (Space n)) (u : Space n → ℝ) (G : Space n → Yau.RIdx n → ℝ) : Prop :=
  MemLp u 2 (volume.restrict O) ∧ (∀ i, MemLp (fun x => G x i) 2 (volume.restrict O)) ∧
    ∃ v : ℕ → Space n → ℝ,
      (∀ k, ContDiff ℝ ∞ (v k) ∧ HasCompactSupport (v k) ∧ tsupport (v k) ⊆ O) ∧
      Tendsto (fun k => (∫ x in O, |v k x-u x|^2) +
        ∑ i, ∫ x in O, |d (v k) x i-G x i|^2) atTop (𝓝 0)

/-- V₂ energy class with genuine weak derivatives and a.e. H¹₀ spatial trace. -/
def Energy (O : Set (Space n)) (a b : ℝ) (u : Point n → ℝ)
    (G : Point n → Yau.RIdx n → ℝ) : Prop :=
  MemLp u 2 (productVolume O (Set.Ioo a b)) ∧
  (∀ i, MemLp (fun p => G p i) 2 (productVolume O (Set.Ioo a b))) ∧
  WeakGradient O (Set.Ioo a b) u G ∧
  (∀ᵐ t ∂volume.restrict (Set.Ioo a b), H10 O (fun x => u (x,t)) (fun x => G (x,t))) ∧
  ∃ C : ℝ, ∀ᵐ t ∂volume.restrict (Set.Ioo a b), (∫ x in O, |u (x,t)|^2) ≤ C

def InitialTrace (O : Set (Space n)) (a : ℝ) (u : Point n → ℝ) (u0 : Space n → ℝ) : Prop :=
  Tendsto (fun t => ∫ x in O, |u (x,t)-u0 x|^2) (𝓝[>] a) (𝓝 0)

/-- Distributional form of the displayed nondivergence operator. The drift
correction b^j-∂i a^(ij) is computed, not chosen. -/
def WeakEquation (O : Set (Space n)) (I : Set ℝ) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (f u : Point n → ℝ)
    (G : Point n → Yau.RIdx n → ℝ) : Prop :=
  ∀ φ : Point n → ℝ, Test (O ×ˢ I) φ →
    (∫ p, -u p * deriv (fun t => φ (p.1,t)) p.2 +
      (∑ i, ∑ j, a p i j * G p j * d (fun x => φ (x,p.2)) p.1 i) -
      (∑ j, (b p j - ∑ i, d (fun x => a (x,p.2) i j) p.1 i) * G p j * φ p)
        ∂productVolume O I) = ∫ p, f p * φ p ∂productVolume O I

/-- Local energy class on an open time interval, with no boundary trace condition.
Suitable for the homogeneous difference extended across zero in flow:670. -/
def LocalEnergy (O : Set (Space n)) (I : Set ℝ) (u : Point n → ℝ)
    (G : Point n → Yau.RIdx n → ℝ) : Prop :=
  WeakGradient O I u G ∧ ∀ (V : Set (Space n)) c e,
    IsOpen V → IsCompact (closure V) → closure V ⊆ O → Set.Icc c e ⊆ I →
    MemLp u 2 (productVolume V (Set.Ioo c e)) ∧
      (∀ i, MemLp (fun p => G p i) 2 (productVolume V (Set.Ioo c e)))

end Yau.Parabolic
