import Yau.Geometry.ParabolicCalculus
import Yau.Blueprint.NormalizationTargets

/-! Scheduled-internal, unproved planning targets for L05, L16 and L15/L23.
No declaration in this file is an axiom or an available analytic theorem.
Source acquisition and the exact remaining bridges are in ParabolicLeafLocks.md. -/
open MeasureTheory Filter
open scoped Topology ContDiff Matrix ComplexOrder Matrix.Norms.Frobenius
noncomputable section
namespace Yau.ParabolicCandidates
open Yau.Parabolic

/-- A genuine modulus for the derivative coefficients of F, not a free
regularity predicate. -/
def Modulus (modulus : ℝ → ℝ) : Prop :=
  modulus 0 = 0 ∧ (∀ r, 0 ≤ r → 0 ≤ modulus r) ∧ MonotoneOn modulus (Set.Ici 0) ∧
    Tendsto modulus (𝓝[≥] 0) (𝓝 0)

def rankOne (v : Yau.RIdx n → ℝ) : Sym n := sym (fun i j => v i * v j)

/-- Chu §5 H1, including the bounded value at the space-time origin.
Ellipticity is the derivative in symmetric rank-one directions. -/
def ChuH1 (E U : Set (Sym n)) (F : Sym n → Point n → ℝ)
    (lam upper K β : ℝ) : Prop :=
  IsOpen U ∧ E ⊆ U ∧
  ContDiffOn ℝ 1 (fun z : Sym n × Point n => F z.1 z.2) (U ×ˢ backward 1) ∧
  (∀ A ∈ E, ∀ p ∈ backward 1, ∀ v : Yau.RIdx n → ℝ,
    lam * (∑ i, (v i)^2) ≤ fderiv ℝ (fun B => F B p) A (rankOne v) ∧
    fderiv ℝ (fun B => F B p) A (rankOne v) ≤ upper * (∑ i, (v i)^2)) ∧
  (∀ A ∈ E, ∀ B ∈ E, ∀ p ∈ backward 1,
    (F A p + F B p)/2 ≤ F ((1/2 : ℝ) • (A+B)) p) ∧
  (∀ A ∈ E, ∀ p ∈ backward 1, ∀ q ∈ backward 1,
    |F A p-F A q| ≤ K * holderWeight β p q) ∧
  ∀ A ∈ E, |F A (0,0)| ≤ K

/-- Chu §5 H2(1)-(3), all on the actual symmetric matrix space. -/
def ChuH2 (T : Sym n → Point n → Sym n) (K β : ℝ) : Prop :=
  (∀ A, ∀ p ∈ backward 1, ∀ q ∈ backward 1,
    ‖T A p-T A q‖ ≤ K * (‖A‖+1) * holderWeight β p q) ∧
  (∀ p ∈ backward 1, ∀ A B, T (A+B) p = T A p + T B p) ∧
  (∀ p ∈ backward 1, ∀ c : ℝ, ∀ A, T (c • A) p = c • T A p) ∧
  ∀ A : Sym n, (A : Mat n).PosSemidef → ∀ p ∈ backward 1,
    (T A p : Mat n).PosSemidef ∧ K⁻¹ * ‖A‖ ≤ ‖T A p‖ ∧ ‖T A p‖ ≤ K * ‖A‖

/-- Chu §5 H3, including the origin bound. -/
def ChuH3 (S : Point n → Sym n) (K β : ℝ) : Prop :=
  ‖S (0,0)‖ ≤ K ∧ ∀ p ∈ backward 1, ∀ q ∈ backward 1,
    ‖S p-S q‖ ≤ K * holderWeight β p q

def ChuDerivativeModulus (E : Set (Sym n)) (F : Sym n → Point n → ℝ)
    (modulus : ℝ → ℝ) : Prop :=
  ∀ A ∈ E, ∀ B ∈ E, ∀ p ∈ backward 1, ∀ q ∈ backward 1,
    ∀ V : Sym n, ‖V‖ ≤ 1 →
      |fderiv ℝ (fun N => F N p) A V - fderiv ℝ (fun N => F N q) B V| ≤
        modulus (‖A-B‖ + parabolicDistance p q)

/-- L05: Chu Theorem 5.1, with all §5 assumptions explicit and the sharp
exponent min(α₀,β₀). The output constant precedes E,F,S,T,f,u: its
permitted dependence is exactly the displayed numerical data and modulus.
Equivalent matrix/Hölder norm conventions still require the lock's bridge. -/
def ChuTransformedHessian : Prop :=
  ∀ n : ℕ, 0 < n → ∀ α β lam upper K fBound uBound : ℝ,
    0 < α → α < 1 → 0 < β → β < 1 → 0 < lam → lam ≤ upper → 0 < K →
    0 ≤ fBound → 0 ≤ uBound → ∀ modulus : ℝ → ℝ, Modulus modulus →
    ∃ C : ℝ, 0 < C ∧
      ∀ (E U : Set (Sym n)) (F : Sym n → Point n → ℝ)
        (S : Point n → Sym n) (T : Sym n → Point n → Sym n)
        (f u : Point n → ℝ),
        IsCompact E → Convex ℝ E → E.Nonempty →
        ChuH1 E U F lam upper K β → ChuH2 T K β → ChuH3 S K β →
        ChuDerivativeModulus E F modulus → HolderBound α (backward 1) f fBound →
        C2 (backward 1) u → (∀ p ∈ backward 1, |u p| ≤ uBound) →
        (∀ p ∈ backward 1, S p + T (hessian u p) p ∈ E) →
        (∀ p ∈ backward 1,
          timeD (backward 1) u p - F (S p + T (hessian u p) p) p = f p) →
        SchauderBound (min α β) (backward (1/2)) u C

/-- L05 actual initial-surface specialization at flow:234-264. A is the
background Hermitian chart matrix; Ric(A), S(x,t_+) and f are computed.
The only second-derivative input is the transformed matrix range. -/
def MongeAmpereInitialSchauder : Prop :=
  ∀ n : ℕ, 0 < n → ∀ α β lam upper K B : ℝ,
    0 < α → α < 1 → 0 < β → β < 1 → 0 < lam → lam ≤ upper → 0 < K → 0 ≤ B →
    ∃ C : ℝ, 0 < C ∧
      ∀ (A : Space n → Matrix (Fin n) (Fin n) ℂ) (u : Point n → ℝ),
      ContDiffOn ℝ ∞ A (Metric.ball 0 1) →
      (∀ x ∈ Metric.ball 0 1, (A x).PosDef) →
      let Q := cylinder (Metric.ball 0 1) (-1) 1
      let Q' := cylinder (Metric.ball 0 (1/2)) (-(1/4)) (1/4)
      HolderBound β Q (clampedBackground A) K → HolderBound α Q (backgroundSource A) K →
      C2 Q u → (∀ p ∈ Q, |u p| ≤ B) →
      (∀ p ∈ Q, p.2 ≤ 0 → u p = 0) →
      (∀ p ∈ Q,
        (((clampedBackground A p + complexHessianMap (hessian u p) : Sym n) : Mat n) -
          lam • (1 : Mat n)).PosSemidef ∧
        (upper • (1 : Mat n) -
          ((clampedBackground A p + complexHessianMap (hessian u p) : Sym n) : Mat n)).PosSemidef) →
      (∀ p ∈ Q, timeD Q u p -
        logDetReal (clampedBackground A p + complexHessianMap (hessian u p)) = backgroundSource A p) →
      SchauderBound (min α β) Q' u C

/-- An algebra/calculus bridge, not a second analytic leaf. -/
def ComplexHessianRepresentation : Prop :=
  Yau.Blueprint.ComplexHessianRepresentation

/-- Smooth coefficients on a fixed closed compact cylinder. -/
def SmoothCoefficients (Q : Set (Point n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) : Prop :=
  ContDiffOn ℝ ∞ a Q ∧ ∀ i, ContDiffOn ℝ ∞ (fun p => b p i) Q

/-- L16 III.4.1 consumer: zero-data weak solution, without forcing f=0
at the initial lateral corner. H¹₀ encodes the lateral trace. The constant is
chosen before f. Uniqueness is equality a.e., as required for energy classes. -/
def ZeroDataEnergyExistence : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (O : Set (Space n)), SmoothDomain O → ∀ T lam upper : ℝ,
    0 < T → ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
    SmoothCoefficients (cylinder (closure O) 0 T) a b →
    Elliptic (cylinder (closure O) 0 T) a lam upper →
    ∃ C : ℝ, 0 < C ∧ ∀ f : Point n → ℝ,
      MemLp f 2 (productVolume O (Set.Ioo 0 T)) →
      ∃ (u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ),
        Energy O 0 T u G ∧ InitialTrace O 0 u (fun _ => 0) ∧
        WeakEquation O (Set.Ioo 0 T) a b f u G ∧
        (∫ p, |u p|^2 + ∑ i, |G p i|^2 ∂productVolume O (Set.Ioo 0 T)) ≤
          C * (∫ p, |f p|^2 ∂productVolume O (Set.Ioo 0 T)) ∧
        ∀ v H, Energy O 0 T v H → InitialTrace O 0 v (fun _ => 0) →
          WeakEquation O (Set.Ioo 0 T) a b f v H →
          u =ᵐ[productVolume O (Set.Ioo 0 T)] v

/-- L16 III.12.1 consumer: genuine weak homogeneous interior smoothing on
an open slab crossing zero. No extension-by-zero assertion is smuggled in. -/
def HomogeneousInteriorSmoothing : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (O : Set (Space n)) (l r lam upper : ℝ),
    IsOpen O → l < r → ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
      (u : Point n → ℝ) (G : Point n → Yau.RIdx n → ℝ),
    SmoothCoefficients (O ×ˢ Set.Ioo l r) a b →
    Elliptic (O ×ˢ Set.Ioo l r) a lam upper →
    LocalEnergy O (Set.Ioo l r) u G →
    WeakEquation O (Set.Ioo l r) a b (fun _ => 0) u G →
    ∃ v : Point n → ℝ, ContDiffOn ℝ ∞ v (O ×ˢ Set.Ioo l r) ∧
      u =ᵐ[productVolume O (Set.Ioo l r)] v ∧
      ∀ p ∈ O ×ˢ Set.Ioo l r, linearOp (O ×ˢ Set.Ioo l r) a b v p = 0

/-- L16 IV.5.1 local Cauchy consumer, after actual smooth extension of the
coefficients/source. Outside a spatial compact set we take the Euclidean heat
operator and zero source. Constructing that extension stays in F04. -/
def ZeroInitialCauchySolution : Prop :=
  ∀ n : ℕ, 0 < n → ∀ T lam upper : ℝ, 0 < T →
    ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (f : Point n → ℝ),
    let Q := cylinder Set.univ 0 T
    SmoothCoefficients Q a b → ContDiffOn ℝ ∞ f Q → Elliptic Q a lam upper →
    (∃ K : Set (Space n), IsCompact K ∧ ∀ x ∉ K, ∀ t ∈ Set.Icc 0 T,
      a (x,t) = 1 ∧ b (x,t) = 0 ∧ f (x,t) = 0) →
    ∃ u : Point n → ℝ, ContDiffOn ℝ ∞ u Q ∧ (∀ x, u (x,0) = 0) ∧
      (∃ B : ℝ, ∀ p ∈ Q, |u p| ≤ B) ∧ ∀ p ∈ Q, linearOp Q a b u p = f p

/-- First equation compatibility, expressed using an actual extension p of
both initial and lateral data. No higher corner compatibility is imposed. -/
def Compatible (O : Set (Space n)) (T : ℝ) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (f p : Point n → ℝ) : Prop :=
  ∀ x ∈ frontier O, linearOp (cylinder (closure O) 0 T) a b p (x,0) = f (x,0)

def DirichletData (O : Set (Space n)) (T : ℝ) (u p : Point n → ℝ) : Prop :=
  (∀ x ∈ closure O, u (x,0) = p (x,0)) ∧
    ∀ x ∈ frontier O, ∀ t ∈ Set.Icc 0 T, u (x,t) = p (x,t)

/-- L16 IV.5.2: compatible inhomogeneous linear Dirichlet solution and
closed-slab C^(2+α,1+α/2) estimate. This is also the continuation-bound
consumer at flow:839, where only the first compatibility is available. -/
def CompatibleDirichletSchauder : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (O : Set (Space n)), SmoothDomain O →
    ∀ T α lam upper M : ℝ, 0 < T → 0 < α → α < 1 → 0 < M →
    ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
    let Q := cylinder (closure O) 0 T
    Elliptic Q a lam upper → HolderBound α Q a M →
    (∀ i, HolderBound α Q (fun p => b p i) M) →
    ∃ C : ℝ, 0 < C ∧ ∀ (f p : Point n → ℝ) (F P : ℝ),
      HolderBound α Q f F → SchauderBound α Q p P → Compatible O T a b f p →
      ∃ u : Point n → ℝ, SchauderBound α Q u (C * (F+P)) ∧ DirichletData O T u p ∧
        (∀ z ∈ cylinder O 0 T, linearOp Q a b u z = f z) ∧
        ∀ v : Point n → ℝ, C2 Q v → DirichletData O T v p →
          (∀ z ∈ cylinder O 0 T, linearOp Q a b v z = f z) → Set.EqOn u v Q

/-- L16 IV.5.4 consumer: a uniform inverse bound as ε↓0 on the compatible
zero-data source space f(·,0)=0. Finite-chart commutators and their smallness
are not assumptions or conclusions of this leaf. -/
def UniformSmallTimeInverse : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (O : Set (Space n)), SmoothDomain O →
    ∀ T α lam upper M : ℝ, 0 < T → 0 < α → α < 1 → 0 < M →
    ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ),
    let Q := cylinder (closure O) 0 T
    Elliptic Q a lam upper → HolderBound α Q a M →
    (∀ i, HolderBound α Q (fun p => b p i) M) →
    ∃ C : ℝ, 0 < C ∧ ∀ ε : ℝ, 0 < ε → ε ≤ T →
      ∀ (f : Point n → ℝ) (F : ℝ),
      let Qε := cylinder (closure O) 0 ε
      HolderBound α Qε f F → (∀ x ∈ closure O, f (x,0) = 0) →
      ∃ u : Point n → ℝ, SchauderBound α Qε u (C*F) ∧
        DirichletData O ε u (fun _ => 0) ∧
        ∀ z ∈ cylinder O 0 ε, linearOp Qε a b u z = f z

/-- The local linear Schauder estimate also used for bootstrapping after
Chu at flow:249-265. This auxiliary internal target is not assigned a source
theorem number that has not been checked in the original book. -/
def InteriorLinearSchauder : Prop :=
  ∀ n : ℕ, 0 < n → ∀ α lam upper M : ℝ,
    0 < α → α < 1 → 0 < M → ∃ C : ℝ, 0 < C ∧
    ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
      (f u : Point n → ℝ) (F B : ℝ),
      Elliptic (backward 2) a lam upper → HolderBound α (backward 2) a M →
      (∀ i, HolderBound α (backward 2) (fun p => b p i) M) →
      HolderBound α (backward 2) f F → C2 (backward 2) u →
      (∀ p ∈ backward 2, |u p| ≤ B) →
      (∀ p ∈ backward 2, linearOp (backward 2) a b u p = f p) →
      SchauderBound α (backward 1) u (C * (B+F))

/-- The exact divergence equation for q=exp(v) at flow:826. All terms,
including the coefficient derivatives in the drift, are computed. -/
def ExpDivergenceEquation (Q : Set (Point n)) (a : Point n → Mat n)
    (b : Point n → Yau.RIdx n → ℝ) (R q : Point n → ℝ) : Prop :=
  ∀ p ∈ Q, timeD Q q p -
    (∑ i, d (fun x => ∑ j, (a (x,p.2) i j / q (x,p.2)) *
      d (fun y => q (y,p.2)) x j) p.1 i) =
    (∑ j, (b p j - ∑ i, d (fun x => a (x,p.2) i j) p.1 i) / q p *
      d (fun x => q (x,p.2)) p.1 j) + (q p-1) * R p

/-- L16 III.10.1 actual specialization: the bounded positive smooth interior
solution q of the displayed divergence equation acquires boundary Hölder
control independently of its gradient. The exterior-measure condition is a
separate geometric bridge from SmoothDomain, recorded in the lock. -/
def ExpBoundaryHolder : Prop :=
  ∀ n : ℕ, 0 < n → ∀ (O : Set (Space n)), SmoothDomain O →
    ∀ T lam upper m B : ℝ, 0 < T → 0 < m → m ≤ B →
    ∀ (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ) (R p : Point n → ℝ),
    let Q := cylinder (closure O) 0 T
    SmoothCoefficients Q a b → ContDiffOn ℝ ∞ R Q → ContDiffOn ℝ ∞ p Q →
    Elliptic Q a lam upper →
    ∃ γ C : ℝ, 0 < γ ∧ γ < 1 ∧ 0 < C ∧ ∀ q : Point n → ℝ,
      C2 Q q → ContDiffOn ℝ ∞ q (O ×ˢ Set.Ioc 0 T) →
      (∀ z ∈ Q, m ≤ q z ∧ q z ≤ B) → DirichletData O T q p →
      ExpDivergenceEquation (O ×ˢ Set.Ioc 0 T) a b R q → HolderBound γ Q q C

/-- L15/L23 common local curvature derivative target. This estimate has
no injectivity-radius premise and bounds actual metric contractions of ∇^kRm.
The earlier-time ball has compact closure and a spatial and temporal buffer. -/
def LocalCurvatureDerivatives : Prop :=
  ∀ n : ℕ, 0 < n → ∀ k : ℕ, ∀ K r τ σ : ℝ,
    0 < K → 0 < r → 0 < τ → 0 < σ → ∃ C : ℝ, 0 < C ∧
      ∀ (M : Yau.ComplexManifold n) (h : ℝ → Yau.HermitianField M)
        (p : M.Carrier) (a : ℝ),
      let O := Yau.distBall (h a) p (2*r)
      let I := Set.Icc a (a+2*τ)
      IsOpen O → IsCompact (closure O) →
      Yau.LocalRealRicciFlow h O I σ →
      (∀ x ∈ O, ∀ t ∈ I, Yau.curvatureJetNorm (h t) 0 x ≤ K) →
      ∀ x ∈ Yau.distBall (h a) p r, ∀ t ∈ Set.Icc (a+τ) (a+2*τ),
        Yau.curvatureJetNorm (h t) k x ≤ C

/-- Required normalization bridge before the complex flow consumes the real
curvature theorem. It is an internal calculation, not a cited theorem. -/
def KahlerRealRicciIdentification : Prop :=
  Yau.Blueprint.KahlerRealRicciIdentification

/-- With G=2 Re h the paper complex time gives ∂t G=-Ric_real (σ=1).
Comparison with the standard -2 Ric_real time uses τ=t/2. This is an unproved
general flow bridge; one-dimensional profiles do not establish it. -/
def KahlerFlowRealNormalization : Prop :=
  Yau.Blueprint.KahlerFlowRealNormalization

/-- Geometric bridge needed for the boundary Hölder source, with an actual
uniform fraction of exterior volume at every sufficiently small boundary ball. -/
def SmoothDomainExteriorMeasure : Prop :=
  ∀ n : ℕ, 0 < n → ∀ O : Set (Space n), SmoothDomain O →
    ∃ θ r0 : ℝ, 0 < θ ∧ 0 < r0 ∧ ∀ x ∈ frontier O, ∀ r : ℝ, 0 < r → r ≤ r0 →
      ENNReal.ofReal θ * volume (Metric.ball x r) ≤ volume (Metric.ball x r \ O)

namespace DefinitionChecks

/-- A freely chosen zero T fails the positive-cone lower comparison in H2. -/
theorem zeroTransform_rejected (K β : ℝ) (hK : 0 < K) :
    ¬ ChuH2 (n := 1) (fun _ _ => 0) K β := by
  intro h
  have hp : ((0,0) : Point 1) ∈ backward 1 := by norm_num [backward]
  let A : Sym 1 := ⟨1, IsSelfAdjoint.one (Mat 1)⟩
  have hpos : (A : Mat 1).PosSemidef := Matrix.PosSemidef.one
  have hne : A ≠ 0 := by
    intro hz
    have hh := congrArg (fun A : Sym 1 => (A : Mat 1) (0,0) (0,0)) hz
    norm_num [A] at hh
  have hlo := (h.2.2.2 A hpos (0,0) hp).2.1
  have hstrict := mul_pos (inv_pos.mpr hK) (norm_pos_iff.mpr hne)
  simp only [norm_zero] at hlo
  linarith

/-- The zero bound cannot silently accept a nonzero source. -/
theorem nonzeroSource_rejected (α : ℝ) :
    ¬ HolderBound (n := 1) α Set.univ (fun _ => (1 : ℝ)) 0 := by
  intro h
  have hh := h.2.1 (0,0) (Set.mem_univ _)
  norm_num at hh

/-- A zero boundary extension is incompatible with nonzero forcing at an
initial lateral corner. This restriction belongs to the Schauder target only. -/
theorem nonzeroCorner_rejected (O : Set (Space n)) (T : ℝ)
    (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
    (x : Space n) (hx : x ∈ frontier O) :
    ¬ Compatible O T a b (fun _ => 1) (fun _ => 0) := by
  intro h
  have hh := h x hx
  simp [linearOp, timeD, spatialDD, spatialD] at hh

/-- ∂t really differentiates time; it cannot be replaced by a chosen zero
operator to accept u=t as a homogeneous solution. -/
theorem timeCoordinate_hasResidual :
    linearOp (n := 1) Set.univ (fun _ => 0) (fun _ => 0)
      (fun p => p.2) (0,0) = 1 := by
  simp [linearOp, timeD, spatialDD, spatialD]

end DefinitionChecks

end Yau.ParabolicCandidates
