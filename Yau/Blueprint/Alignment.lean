import Yau.Blueprint.Stages

/-!
Concrete contracts for dynamics.tex:195–664. No polynomial models are premises of
linear alignment: its inputs are the geometric transitions and the clock.
All rates, jumps and propagated weights below are computed from those inputs.
These are planning statements, not proofs of the paper's lemmas.
-/

open scoped Topology Matrix ComplexOrder
open Filter

noncomputable section

attribute [local instance] Classical.propDecidable

namespace Yau.Blueprint.Alignment

open Yau

variable {n : ℕ}

/-- An actual inverse of the late volume clock; `q` is never free data. -/
def ClockParameter (X : KahlerManifold n) (o : Pt X) (_h : Flow X) (ρ : STF X)
    (time : ℝ → ℝ) (s₀ : ℝ) : Prop :=
  0 < s₀ ∧ StrictMonoOn time (Set.Ici s₀) ∧
  (∀ s, s₀ ≤ s → 0 < time s ∧ ρ o (time s) = s) ∧
  Tendsto time atTop atTop

/-- Exact continuous-clock rate input (dynamics.tex:19–25), with no global
upper bound on `q(s)/s`. All occurrences of `q` use the geometric clock speed. -/
def ClockRateInput {X : KahlerManifold n} (o : Pt X) (h : Flow X)
    (time : ℝ → ℝ) (s₀ a₀ b₀ : ℝ) : Prop :=
  MonotoneOn (fun s => clockSpeed o h (time s)) (Set.Ici s₀) ∧
  (∃ c : ℝ, 0 < c ∧ ∀ s, s₀ ≤ s → c ≤ clockSpeed o h (time s)) ∧
  (∀ eps : ℝ, 0 < eps → ∀ S : ℝ, ∃ s : ℝ, max S s₀ ≤ s ∧
    clockSpeed o h (time s) ≤ (2 + eps) * s) ∧
  ∀ s, s₀ ≤ s → b₀ * clockSpeed o h (time (a₀ * s)) ≤ ricciMin o h (time s)

def macroClock (hm : ℝ) (j : ℕ) : ℝ := Real.exp (hm * j)

def sampledSpeed {X : KahlerManifold n} (o : Pt X) (h : Flow X)
    (time : ℝ → ℝ) (hm : ℝ) (j : ℕ) : ℝ :=
  clockSpeed o h (time (macroClock hm j))

/-- Flags are restricted to indices where the left growth endpoint exists.
All conclusions start strictly after this finite boundary. -/
def Flag (Q : ℕ → ℝ) (N : ℕ) (M : ℝ) (j : ℕ) : Prop :=
  N ≤ j ∧ M < Real.log (Q (j + 1)) - Real.log (Q (j - N))

def Bad (Q : ℕ → ℝ) (N : ℕ) (M : ℝ) (j : ℕ) : Prop :=
  ∃ f, Flag Q N M f ∧ f - N ≤ j ∧ j < f + 1 + N

def Regular (Q : ℕ → ℝ) (N : ℕ) (M : ℝ) (j : ℕ) : Prop := ¬ Bad Q N M j

/-- Maximal connected components of the expanded union, including its boundaries. -/
def FullBadComponent (Q : ℕ → ℝ) (N : ℕ) (M : ℝ) (u v : ℕ) : Prop :=
  u < v ∧ (u = 0 ∨ Regular Q N M (u - 1)) ∧ Regular Q N M v ∧
    ∀ j, u ≤ j → j < v → Bad Q N M j

def InfiniteBadComponent (Q : ℕ → ℝ) (N : ℕ) (M : ℝ) (u : ℕ) : Prop :=
  (u = 0 ∨ Regular Q N M (u - 1)) ∧ ∀ j, u ≤ j → Bad Q N M j

/-- The subdivision is a formula, including the single bad step. -/
def pieces (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ) (j : ℕ) : ℕ :=
  if Bad Q N M j then 1 else
    max 1 (Nat.ceil ((macroClock hm (j + 1) - macroClock hm j) /
      Real.sqrt (macroClock hm j)))

def offset (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ) (j₀ j : ℕ) : ℕ :=
  ∑ r ∈ Finset.range (j - j₀), pieces Q N M hm (j₀ + r)

/-- Canonical macroIndex containing global step `k`; natural infimum removes any choice. -/
def macroAt (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ) (j₀ k : ℕ) : ℕ :=
  sInf {j | j₀ ≤ j ∧ k < offset Q N M hm j₀ (j + 1)}

def slotAt (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ) (j₀ k : ℕ) : ℕ :=
  k - offset Q N M hm j₀ (macroAt Q N M hm j₀ k)

def gridClock (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ) (j₀ k : ℕ) : ℝ :=
  let j := macroAt Q N M hm j₀ k
  macroClock hm j + (slotAt Q N M hm j₀ k : ℝ) /
    pieces Q N M hm j * (macroClock hm (j + 1) - macroClock hm j)

/-- Canonical indexing equations exposed for downstream use. -/
def GridLayout (Q : ℕ → ℝ) (N : ℕ) (M hm : ℝ) (j₀ : ℕ) : Prop :=
  let s := gridClock Q N M hm j₀
  s 0 = macroClock hm j₀ ∧ StrictMono s ∧ Tendsto s atTop atTop ∧
  (∀ k, j₀ ≤ macroAt Q N M hm j₀ k ∧
    slotAt Q N M hm j₀ k < pieces Q N M hm (macroAt Q N M hm j₀ k) ∧
    k = offset Q N M hm j₀ (macroAt Q N M hm j₀ k) + slotAt Q N M hm j₀ k) ∧
  (∀ j, j₀ ≤ j → s (offset Q N M hm j₀ j) = macroClock hm j) ∧
  ∃ ch Ch : ℝ, 0 < ch ∧ 0 < Ch ∧ ∀ k,
    ch * Real.sqrt (s k) ≤ s (k + 1) - s k ∧
    s (k + 1) - s k ≤ (Real.exp hm - 1) * s k ∧
    (Regular Q N M (macroAt Q N M hm j₀ k) →
      s (k + 1) - s k ≤ Ch * Real.sqrt (s k))

/-- Frames contain matrices only, with no rate/weight fields. -/
structure Frames (n : ℕ) where
  start : ℕ → Herm n
  finish : ℕ → Herm n

def Unitary (A : Herm n) : Prop := A.conjTranspose * A = 1 ∧ A * A.conjTranspose = 1

def derivativeMatrix (F : ComplexVector n → ComplexVector n) : Herm n :=
  Matrix.toEuclideanLin.symm (centerDeriv F).toLinearMap

def transformedDerivative (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (E : Frames n) (k : ℕ) : Herm n :=
  (E.finish k).conjTranspose * derivativeMatrix (F (tk k) (tk (k + 1))) * E.start k

def singularLength (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (E : Frames n) (k : ℕ) (i : Fin n) : ℝ :=
  ‖transformedDerivative F tk E k i i‖

def diagonal (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (E : Frames n) (k : ℕ) : Herm n :=
  Matrix.diagonal (fun i => (singularLength F tk E k i : ℂ))

/-- The logarithmic rates are calculated from the actual derivative's SVD. -/
def rate (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (E : Frames n) (k : ℕ) (i : Fin n) : ℝ :=
  -2 * Real.log (singularLength F tk E k i) / Real.log (tk (k + 1) / tk k)

def jump (E : Frames n) (k : ℕ) : Herm n :=
  (E.start (k + 1)).conjTranspose * E.finish k

def SingularFrames (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (E : Frames n) : Prop :=
  ∀ k, 0 < tk k ∧ tk k < tk (k + 1) ∧ Unitary (E.start k) ∧ Unitary (E.finish k) ∧
    transformedDerivative F tk E k = diagonal F tk E k ∧
    (∀ i, 0 < singularLength F tk E k i ∧ singularLength F tk E k i ≤ 1) ∧
    Antitone (singularLength F tk E k)

/-- The covector Loewner jump, including the actual shared-frame matrix. -/
def RateOrder (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (E : Frames n) : Prop :=
  (∀ k (v : Fin n → ℂ),
    ∑ l, rate F tk E k l * ‖(v ᵥ* jump E k) l‖ ^ 2 ≤
      ∑ i, rate F tk E (k + 1) i * ‖v i‖ ^ 2) ∧
  ∀ i, Monotone (fun k => rate F tk E k i)

def multiplier (scale K : ℝ) (j : ℕ) : ℝ :=
  scale * ∏ r ∈ Finset.range j, (1 + K / ((r + 1 : ℕ) : ℝ) ^ 2)

def theta (Q : ℕ → ℝ) (j : ℕ) : ℝ := Q j / (j : ℝ) ^ 2

/-- Finite vertices in one macroIndex. Edges cannot leave that macroIndex. -/
def vertices (p : ℕ) : Finset (ℕ × Fin n) := (Finset.range p).product Finset.univ

def Passage (μ : ℕ → Fin n → ℝ) (off : ℕ) (eps θ : ℝ)
    (a b : ℕ × Fin n) : Prop :=
  (a.1 = b.1 ∨ a.1 + 1 = b.1) ∧ μ (off + a.1) a.2 - eps * θ ≤ μ (off + b.1) b.2

def Reach (p : ℕ) (μ : ℕ → Fin n → ℝ) (off : ℕ) (eps θ : ℝ)
    (a b : ℕ × Fin n) : Prop :=
  Relation.ReflTransGen (fun x y => x ∈ vertices p ∧ y ∈ vertices p ∧
    Passage μ off eps θ x y) a b

def rawWeight (μ : ℕ → Fin n → ℝ) (off : ℕ) (lam θ : ℝ)
    (a : ℕ × Fin n) : ℝ := lam * (μ (off + a.1) a.2 - θ)

/-- Literal maximum of the finite predecessor raw weights. The inserted zero-path
vertex also makes this total for invalid slots; contracts use only valid slots. -/
def propagatedWeight (p : ℕ) (μ : ℕ → Fin n → ℝ) (off : ℕ) (lam eps θ : ℝ)
    (b : ℕ × Fin n) : ℝ :=
  let candidates := insert (rawWeight μ off lam θ b)
    (((vertices p).filter (fun a => Reach p μ off eps θ a b)).image
      (rawWeight μ off lam θ))
  candidates.sup' (Finset.insert_nonempty _ _) id

def weight (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps : ℝ) (j₀ : ℕ)
    (μ : ℕ → Fin n → ℝ) (k : ℕ) (i : Fin n) : ℝ :=
  let j := macroAt Q N M hm j₀ k
  propagatedWeight (pieces Q N M hm j) μ (offset Q N M hm j₀ j)
    (multiplier scale K j) eps (theta Q j) (slotAt Q N M hm j₀ k, i)

/-- Actual matrices; inverse jumps are not independently supplied. -/
structure Changes (n : ℕ) where
  plus : ℕ → Herm n
  minus : ℕ → Herm n

def alignedJump (E : Frames n) (L : Changes n) (k : ℕ) : Herm n :=
  L.minus (k + 1) * jump E k * (L.plus k)⁻¹

def ChangeAt (D : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (macroIndex : ℕ → ℕ)
    (S : ℕ → ℝ) (C c : ℝ) (L : Changes n) (k : ℕ) : Prop :=
  (∀ i, L.plus k i i = 1) ∧
  (∀ i l, i ≠ l → L.plus k i l ≠ 0 → w k i < w k l) ∧
  L.minus k = (D k)⁻¹ * L.plus k * D k ∧
  L.plus k * D k * (L.minus k)⁻¹ = D k ∧
  matOpNorm (L.plus k) + matOpNorm ((L.plus k)⁻¹) ≤ (1 + (macroIndex k : ℝ)) ^ C ∧
  matOpNorm (L.minus k - 1) ≤ (1 + (macroIndex k : ℝ)) ^ C *
    Real.exp (-c * Real.sqrt (S (macroIndex k)) / (macroIndex k : ℝ) ^ 2)

def JumpAt (E : Frames n) (w : ℕ → Fin n → ℝ) (L : Changes n) (k : ℕ) : Prop :=
  ∀ i l, w (k + 1) i < w k l → alignedJump E L k i l = 0

/-- Uniform finite terminal problems and one common coefficientwise subsequence
on every infinite regular tail. Finite solutions are not falsely required to be
identical before taking a subsequence. -/
def AlignmentRuns (E : Frames n) (D : ℕ → Herm n) (w : ℕ → Fin n → ℝ)
    (reg : ℕ → Prop) (macroIndex : ℕ → ℕ) (S : ℕ → ℝ) : Prop :=
  ∃ C c : ℝ, 0 < C ∧ 0 < c ∧
    (∀ a len : ℕ, 0 < len → (∀ r, r < len → reg (a + r)) →
      ∃ L : Changes n, L.plus (a + len - 1) = 1 ∧
        (∀ r, r < len → ChangeAt D w macroIndex S C c L (a + r)) ∧
        ∀ r, r + 1 < len → JumpAt E w L (a + r)) ∧
    ∀ a : ℕ, (∀ k, a ≤ k → reg k) →
      ∃ (L : Changes n) (finite : ℕ → Changes n) (subseq : ℕ → ℕ),
        StrictMono subseq ∧
        (∀ k, a ≤ k → ChangeAt D w macroIndex S C c L k ∧ JumpAt E w L k) ∧
        (∀ H, (finite H).plus (a + H) = 1 ∧
          (∀ r, r ≤ H → ChangeAt D w macroIndex S C c (finite H) (a + r)) ∧
          ∀ r, r < H → JumpAt E w (finite H) (a + r)) ∧
        ∀ k i l, a ≤ k →
          Tendsto (fun H => (finite (subseq H)).plus k i l) atTop (𝓝 (L.plus k i l)) ∧
          Tendsto (fun H => (finite (subseq H)).minus k i l) atTop (𝓝 (L.minus k i l))

/-- Window-scale lower and upper bounds needed for the exact bad-component
reset. The weaker `b Q_j` bounds alone would lose the payment constant. -/
def WindowRateBounds (Q : ℕ → ℝ) (N : ℕ) (M hm b₀ : ℝ) (j₀ : ℕ)
    (μ : ℕ → Fin n → ℝ) : Prop :=
  ∀ k i, Regular Q N M (macroAt Q N M hm j₀ k) →
    b₀ * Q (macroAt Q N M hm j₀ k - N) ≤ μ k i ∧
      μ k i ≤ Q (macroAt Q N M hm j₀ k + 1)

/-- All conclusions of rate propagation, including the across-macroIndex rule. -/
def WeightEstimates (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps b : ℝ) (j₀ : ℕ)
    (μ : ℕ → Fin n → ℝ) : Prop :=
  let macroIndex := macroAt Q N M hm j₀
  let w := weight Q N M hm scale K eps j₀ μ
  (∀ k i, Regular Q N M (macroIndex k) →
    b * Q (macroIndex k) ≤ μ k i ∧ μ k i ≤ b⁻¹ * Q (macroIndex k) ∧ 1 ≤ w k i ∧
    multiplier scale K (macroIndex k) * (μ k i - theta Q (macroIndex k)) ≤ w k i ∧
    w k i ≤ multiplier scale K (macroIndex k) * (μ k i - 0.9 * theta Q (macroIndex k))) ∧
  (∀ k i l, Regular Q N M (macroIndex k) → Regular Q N M (macroIndex (k + 1)) →
    μ k l - eps * theta Q (macroIndex k) ≤ μ (k + 1) i → w k l ≤ w (k + 1) i) ∧
  (∀ k i (β : Fin n →₀ ℕ), Regular Q N M (macroIndex k) →
    2 ≤ β.sum (fun _ e => e) → w k i < ∑ l, (β l : ℝ) * w k l →
    0.8 * theta Q (macroIndex k) < ∑ l, (β l : ℝ) * μ k l - μ k i) ∧
  ∃ B, ∀ j, multiplier scale K j ≤ B

/-- Restriction of E03's actual joint cotangent/time Levi inequality. -/
def JointPositiveClock (X : KahlerManifold n) (h : Flow X) : Prop :=
  ∀ (x : Pt X) (z ξ : ComplexVector n) (w : ℂ), z ∈ chartTarget x →
    (leviMatrix (fun q : ComplexVector n × ComplexVector n × ℂ =>
      dualNormChart (h (Real.exp (2 * q.2.2.re))) x q.1 q.2.1) (z, ξ, w)
      (Sum.elim (Sum.elim (fun i => (stdVec i, 0, 0))
        (fun i => (0, stdVec i, 0))) (fun _ : Unit => (0, 0, 1)))).PosSemidef

/-- Geometric Y03. The clock, flags and subdivision precede the SVD, weights
and alignment. `M` is freely enlargeable before the eventual threshold.
E03 supplies rate-form order; C04 and C07 supply the clock and transitions.
The existential late start covers the left endpoint of every influencing
flag, two N-windows back, on the actual inverse-clock domain. -/
def Y03 : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector n → Pt X)
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (f : ℝ → Pt X → ComplexVector n),
    FlowStage X o h U P ρ → RicciWindows X o h ρ →
    JointPositiveClock X h →
    ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f →
    ∃ (time : ℝ → ℝ) (s₀ a₀ b₀ : ℝ), ClockParameter X o h ρ time s₀ ∧
      0 < a₀ ∧ a₀ < 1 ∧ 0 < b₀ ∧
      ClockRateInput o h time s₀ a₀ b₀ ∧
      ∀ hm, 0 < hm → hm < 1 → ∃ N : ℕ, 1 ≤ N ∧ Real.exp (-hm * N) ≤ a₀ ∧
        ∀ M : ℝ, 0 < M → ∃ scale K eps b : ℝ, 0 < scale ∧ 0 < K ∧ 0 < eps ∧
          eps < 1 / (10 * (n + 1 : ℝ)) ∧ 0 < b ∧ ∃ jLate : ℕ, 2 * N < jLate ∧
          s₀ ≤ macroClock hm (jLate - 2 * N) ∧
          ∀ j₀, jLate ≤ j₀ → Regular (sampledSpeed o h time hm) N M j₀ →
            let Q := sampledSpeed o h time hm
            let s := gridClock Q N M hm j₀
            let tk := fun k => time (s k)
            GridLayout Q N M hm j₀ ∧ (∀ k, s₀ ≤ s k ∧ t₀ ≤ tk k) ∧
            ∃ E : Frames n, SingularFrames F tk E ∧ RateOrder F tk E ∧
              (∀ k, ∑ i, rate F tk E k i =
                (s (k + 1) - s k) / Real.log (tk (k + 1) / tk k)) ∧
              WindowRateBounds Q N M hm b₀ j₀ (rate F tk E) ∧
              WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E) ∧
              AlignmentRuns E (diagonal F tk E)
                (weight Q N M hm scale K eps j₀ (rate F tk E))
                (fun k => Regular Q N M (macroAt Q N M hm j₀ k))
                (macroAt Q N M hm j₀) (macroClock hm)

/-- Scalar Taylor-jet equality, fixing every derivative through order `d`. -/
def ScalarJetEq (f g : ComplexVector n → ℂ) (d : ℕ) : Prop :=
  ∀ m ≤ d, iteratedFDeriv ℂ m f 0 = iteratedFDeriv ℂ m g 0

def scalarEval (P : MvPolynomial (Fin n) ℂ) (z : ComplexVector n) : ℂ :=
  MvPolynomial.eval (fun i => z i) P

def transitionDet (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (t t' : ℝ) (z : ComplexVector n) : ℂ :=
  LinearMap.det (fderiv ℂ (F t t') z).toLinearMap

/-- Literal polynomial integration in the last coordinate. -/
def integrateLast (last : Fin n) (E : MvPolynomial (Fin n) ℂ) : MvPolynomial (Fin n) ℂ :=
  ∑ β ∈ E.support, MvPolynomial.monomial (β + Finsupp.single last 1)
    (E.coeff β / (β last + 1 : ℂ))

def volumeMap (last : Fin n) (E : MvPolynomial (Fin n) ℂ) : PolyMap n :=
  fun i => if i = last then integrateLast last E else MvPolynomial.X i

/-- The actual coherent volume construction, not an arbitrary correction field.
`B k l` is the unique truncated Taylor polynomial of `P_l ∘ F_{k,l}`.
The `HasSum` clauses identify every coefficient of the infinite tail. -/
def CoherentVolume (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk s : ℕ → ℝ) (d : ℕ) (r : ℝ) (last : Fin n)
    (P : ℕ → ComplexVector n → ℂ) (B : ℕ → ℕ → MvPolynomial (Fin n) ℂ)
    (ell E : ℕ → MvPolynomial (Fin n) ℂ) (A Ainv V : ℕ → PolyMap n) : Prop :=
  0 < r ∧
  (∀ k, P k 0 = 0 ∧ DifferentiableOn ℂ (P k) (Metric.ball 0 r) ∧
    ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      Complex.exp (P k z) = transitionDet F (tk k) (tk (k + 1)) z /
        transitionDet F (tk k) (tk (k + 1)) 0) ∧
  (∀ k l, k ≤ l → (B k l).totalDegree ≤ d - 1 ∧ (B k l).coeff 0 = 0 ∧
    ScalarJetEq (scalarEval (B k l)) (fun z => P l (F (tk k) (tk l) z)) (d - 1)) ∧
  (∀ k, (ell k).totalDegree ≤ d - 1 ∧ (ell k).coeff 0 = 0 ∧
    (∀ β, HasSum (fun r : ℕ => (B k (k + r)).coeff β) ((ell k).coeff β)) ∧
    ScalarJetEq (scalarEval (ell k))
      (fun z => P k z + scalarEval (ell (k + 1)) (F (tk k) (tk (k + 1)) z)) (d - 1) ∧
    (E k).totalDegree ≤ d - 1 ∧
    ScalarJetEq (scalarEval (E k)) (fun z => Complex.exp (scalarEval (ell k) z)) (d - 1) ∧
    A k = volumeMap last (E k) ∧
    (A k).FixesZero ∧ (Ainv k).FixesZero ∧ (A k).linearPart = 1 ∧
    (A k).degree ≤ d ∧ (Ainv k).degree ≤ d ∧
    PolyMap.JetEq ((A k).comp (Ainv k)) PolyMap.id d ∧
    PolyMap.JetEq ((Ainv k).comp (A k)) PolyMap.id d ∧
    (V k).degree ≤ d ∧ IsConstantVolumeJet (V k) d ∧
    GermJetEq (fun z => (A (k + 1)).eval
      (F (tk k) (tk (k + 1)) ((Ainv k).eval z))) (V k).eval d) ∧
  ∃ C : ℝ, 0 < C ∧ ∀ k,
    (∑ β ∈ (ell k).support, ‖(ell k).coeff β‖) +
      (A k).coeffNorm + (Ainv k).coeffNorm ≤ (1 + |s k|) ^ C

/-- Y05: coherent volume normalization on a genuine geometric grid. It is an
upstream construction used by Y06/Y01, with no polynomial-model premise. -/
def Y05 : Prop :=
  ∀ (n : ℕ) (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X)
    (U P ρ : STF X) (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector n → Pt X)
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (f : ℝ → Pt X → ComplexVector n),
    FlowStage X o h U P ρ → RicciWindows X o h ρ →
    ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f →
    ∀ d : ℕ, 2 ≤ d → ∀ hm, 0 < hm → hm < 1 → ∀ tk : ℕ → ℝ,
      StrictMono tk → (∀ k, t₀ ≤ tk k) →
      let s := fun k => ρ o (tk k)
      Tendsto s atTop atTop → (∀ k, 0 < s k) →
      (∃ ch : ℝ, 0 < ch ∧ ∀ k, ch * Real.sqrt (s k) ≤ s (k + 1) - s k ∧
        s (k + 1) - s k ≤ (Real.exp hm - 1) * s k) →
      ∃ (r : ℝ) (logs : ℕ → ComplexVector n → ℂ)
        (B : ℕ → ℕ → MvPolynomial (Fin n) ℂ) (ell E : ℕ → MvPolynomial (Fin n) ℂ)
        (A Ainv V : ℕ → PolyMap n), r ≤ r₁ ∧
        CoherentVolume F tk s d r ⟨n - 1, by omega⟩ logs B ell E A Ainv V

/-- Polynomial induced by an actual matrix. -/
def linearPolynomial (A : Herm n) : PolyMap n :=
  fun i => ∑ l, MvPolynomial.C (A i l) * MvPolynomial.X l

def Allowed (g : PolyMap n) (w : Fin n → ℝ) : Prop :=
  ∀ i (β : Fin n →₀ ℕ), 2 ≤ β.sum (fun _ e => e) → (g i).coeff β ≠ 0 →
    ∑ l, (β l : ℝ) * w l ≤ w i

/-- The primary chart derivative; volume and nonlinear corrections are tangent
 to the identity. At a bad start retain the previous regular end, if any. -/
def primaryDerivative (reg : ℕ → Prop) (E : Frames n) (L : Changes n) (k : ℕ) : Herm n :=
  if reg k then L.minus k * (E.start k).conjTranspose else
    if 0 < k ∧ reg (k - 1) then L.plus (k - 1) * (E.finish (k - 1)).conjTranspose else 1

/-- Total local coordinate germ whose degree-`d` truncation is `H_k`.
Every nonlinear factor comes from the coherent volume and homological outputs. -/
def totalCoordinateGerm (A : ℕ → PolyMap n) (E : Frames n) (L : Changes n)
    (reg : ℕ → Prop) (correction : ℕ → PolyMap n) (k : ℕ)
    (z : ComplexVector n) : ComplexVector n :=
  (correction k).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ)
    (primaryDerivative reg E L k) ((A k).eval z))

/-- This is the additional construction invariant required in Y01; bare
`PolynomialModels` does not imply forward degree control. The regular model
and aligned linear jump are tied to the same `G` and actual geometric SVD. -/
def RegularModelCompatibility (F : ℝ → ℝ → ComplexVector n → ComplexVector n)
    (tk : ℕ → ℝ) (Q : ℕ → ℝ) (N : ℕ) (M hm scale K eps : ℝ) (j₀ Dstar : ℕ)
    (E : Frames n) (L : Changes n) (H G Ginv g : ℕ → PolyMap n) : Prop :=
  let macroIndex := macroAt Q N M hm j₀
  let reg := fun k => Regular Q N M (macroIndex k)
  let w := weight Q N M hm scale K eps j₀ (rate F tk E)
  SingularFrames F tk E ∧ RateOrder F tk E ∧
  (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ k, reg k →
    ChangeAt (diagonal F tk E) w macroIndex (macroClock hm) C c L k ∧
      (reg (k + 1) → JumpAt E w L k)) ∧
  (∀ k, (H k).linearPart = primaryDerivative reg E L k) ∧
  (∀ k, (G k).degree ≤ Dstar ∧ (Ginv k).degree ≤ Dstar) ∧
  ∀ k, reg k →
    let J := if reg (k + 1) then alignedJump E L k else 1
    G k = (linearPolynomial J).comp (g k) ∧
      (g k).FixesZero ∧ (g k).linearPart = diagonal F tk E k ∧ Allowed (g k) (w k) ∧
      (g k).jacDet = MvPolynomial.C (diagonal F tk E k).det

/-- Actual volume-normalized transition before the aligned jump. -/
def normalizedRegularTransition
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (tk : ℕ → ℝ)
    (A Ainv : ℕ → PolyMap n) (E : Frames n) (L : Changes n) (k : ℕ)
    (z : ComplexVector n) : ComplexVector n :=
  Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (L.plus k * (E.finish k).conjTranspose)
    ((A (k + 1)).eval (F (tk k) (tk (k + 1))
      ((Ainv k).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (E.start k * (L.minus k)⁻¹) z))))

def forbiddenProjection (w : Fin n → ℝ) (X : PolyMap n) : PolyMap n :=
  fun i => ∑ β ∈ (X i).support,
    if w i < ∑ l, (β l : ℝ) * w l then MvPolynomial.monomial β ((X i).coeff β) else 0

/-- The complete conjugation is expanded before projection. No support
restriction is imposed on the incoming homogeneous polynomial. -/
def backwardOperator (D J : Herm n) (w : Fin n → ℝ) (X : PolyMap n) : PolyMap n :=
  forbiddenProjection w ((linearPolynomial D⁻¹).comp
    ((linearPolynomial J⁻¹).comp (X.comp (linearPolynomial (J * D)))))

def Homogeneous (X : PolyMap n) (m : ℕ) : Prop :=
  ∀ i (β : Fin n →₀ ℕ), (X i).coeff β ≠ 0 → β.sum (fun _ e => e) = m

structure JetData (n : ℕ) where
  correction : ℕ → PolyMap n
  inverseJet : ℕ → PolyMap n
  model : ℕ → PolyMap n
  inverseModel : ℕ → PolyMap n

/-- Complete jet identity, forbidden/allowed split, inverse jets, and the
volume identity obtained by backward determinant induction. -/
def RegularJetSolution (Fhat : ℕ → ComplexVector n → ComplexVector n)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (active : ℕ → Prop)
    (d Dstar : ℕ) (s : ℕ → ℝ) (C : ℝ) (Q : JetData n) : Prop :=
  (∀ k, ¬ active k → Q.correction k = PolyMap.id ∧ Q.inverseJet k = PolyMap.id) ∧
  ∀ k, active k →
    (Q.correction k).linearPart = 1 ∧ (Q.correction k).degree ≤ d ∧
    IsConstantVolumeJet (Q.correction k) d ∧
    (Q.inverseJet k).degree ≤ d ∧ (Q.inverseJet k).FixesZero ∧
    PolyMap.JetEq ((Q.correction k).comp (Q.inverseJet k)) PolyMap.id d ∧
    PolyMap.JetEq ((Q.inverseJet k).comp (Q.correction k)) PolyMap.id d ∧
    (∀ i (β : Fin n →₀ ℕ), 2 ≤ β.sum (fun _ e => e) →
      (Q.correction k i).coeff β ≠ 0 → w k i < ∑ l, (β l : ℝ) * w k l) ∧
    (Q.model k).FixesZero ∧ (Q.model k).linearPart = D k ∧ Allowed (Q.model k) (w k) ∧
    IsPolyAutomorphism (Q.model k) (Q.inverseModel k) ∧
    (Q.model k).degree ≤ Dstar ∧ (Q.inverseModel k).degree ≤ Dstar ∧
    (Q.model k).jacDet = MvPolynomial.C (D k).det ∧
    GermJetEq (fun z => (Q.model k).eval ((Q.correction k).eval z))
      (fun z => Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) ((J k)⁻¹)
        ((Q.correction (k + 1)).eval (Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) (J k) (Fhat k z)))) d ∧
    (Q.correction k).coeffNorm + (Q.inverseJet k).coeffNorm +
      (Q.model k).coeffNorm + (Q.inverseModel k).coeffNorm ≤ Real.exp (C * Real.sqrt (s k))

/-- Finite terminal identities, uniform bounds, and one common coefficientwise
subsequence for the infinite homological recursion. -/
def RegularJetRuns (Fhat : ℕ → ComplexVector n → ComplexVector n)
    (D J : ℕ → Herm n) (w : ℕ → Fin n → ℝ) (reg : ℕ → Prop)
    (d Dstar : ℕ) (s : ℕ → ℝ) : Prop :=
  ∃ C : ℝ, 0 < C ∧
    (∃ globalJets : JetData n, RegularJetSolution Fhat D J w reg d Dstar s C globalJets) ∧
    (∀ a len : ℕ, 0 < len → (∀ k, a ≤ k → k < a + len → reg k) →
      ∃ Q : JetData n,
        RegularJetSolution Fhat D J w (fun k => a ≤ k ∧ k < a + len) d Dstar s C Q ∧
        Q.correction (a + len) = PolyMap.id) ∧
    ∀ a : ℕ, (∀ k, a ≤ k → reg k) →
      ∃ (Q : JetData n) (finite : ℕ → JetData n) (subseq : ℕ → ℕ),
        StrictMono subseq ∧
        RegularJetSolution Fhat D J w (fun k => a ≤ k) d Dstar s C Q ∧
        (∀ H, RegularJetSolution Fhat D J w (fun k => a ≤ k ∧ k < a + H + 1)
          d Dstar s C (finite H) ∧ (finite H).correction (a + H + 1) = PolyMap.id) ∧
        ∀ k i β, a ≤ k →
          Tendsto (fun H => ((finite (subseq H)).correction k i).coeff β)
            atTop (𝓝 ((Q.correction k i).coeff β)) ∧
          Tendsto (fun H => ((finite (subseq H)).inverseJet k i).coeff β)
            atTop (𝓝 ((Q.inverseJet k i).coeff β)) ∧
          Tendsto (fun H => ((finite (subseq H)).model k i).coeff β)
            atTop (𝓝 ((Q.model k i).coeff β)) ∧
          Tendsto (fun H => ((finite (subseq H)).inverseModel k i).coeff β)
            atTop (𝓝 ((Q.inverseModel k i).coeff β))

/-- Y06 pure construction after the geometric Y03/Y05 outputs. The only
transition in the conclusion is the formula using actual `F`, `A`, SVD frames
and aligned matrices. This does not take polynomial models as input. -/
def Y06 : Prop :=
  ∀ n d : ℕ, 2 ≤ d → ∃ Dstar : ℕ, 1 ≤ Dstar ∧
    ∀ (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (tk : ℕ → ℝ)
      (Qclock : ℕ → ℝ) (N j₀ : ℕ) (M hm scale K eps b b₀ : ℝ)
      (Eframes : Frames n) (L : Changes n) (r : ℝ) (last : Fin n)
      (logs : ℕ → ComplexVector n → ℂ) (B : ℕ → ℕ → MvPolynomial (Fin n) ℂ)
      (ell E : ℕ → MvPolynomial (Fin n) ℂ) (A Ainv V : ℕ → PolyMap n),
      let s := gridClock Qclock N M hm j₀
      let macroIndex := macroAt Qclock N M hm j₀
      let reg := fun k => Regular Qclock N M (macroIndex k)
      let w := weight Qclock N M hm scale K eps j₀ (rate F tk Eframes)
      let D := diagonal F tk Eframes
      let J := fun k => if reg (k + 1) then alignedJump Eframes L k else 1
      0 < hm → hm < 1 → 0 < scale → 0 < K → 0 < eps →
      eps < 1 / (10 * (n + 1 : ℝ)) → 0 < b → 0 < b₀ →
      GridLayout Qclock N M hm j₀ → SingularFrames F tk Eframes → RateOrder F tk Eframes →
      WindowRateBounds Qclock N M hm b₀ j₀ (rate F tk Eframes) →
      WeightEstimates Qclock N M hm scale K eps b j₀ (rate F tk Eframes) →
      (∀ k, F (tk k) (tk (k + 1)) 0 = 0 ∧
        DifferentiableOn ℂ (F (tk k) (tk (k + 1))) (Metric.ball 0 r)) →
      CoherentVolume F tk s d r last logs B ell E A Ainv V →
      (∀ k, ‖transitionDet F (tk k) (tk (k + 1)) 0‖ =
        Real.exp (-(s (k + 1) - s k) / 2)) →
      (∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ k, reg k →
        ChangeAt D w macroIndex (macroClock hm) C c L k ∧ (reg (k + 1) → JumpAt Eframes w L k)) →
      (∀ m ≤ d, ∃ C : ℝ, ∀ k, reg k →
        jetNorm (F (tk k) (tk (k + 1))) m ≤ (1 + s k) ^ C) →
      ∃ kLate : ℕ,
        RegularJetRuns (normalizedRegularTransition F tk A Ainv Eframes L) D J w
          (fun k => kLate ≤ k ∧ reg k) d Dstar s ∧
        ∀ m, 2 ≤ m → m ≤ d → ∃ Cm c : ℝ, 0 < c ∧ ∀ k, kLate ≤ k → reg k →
          ∀ X : PolyMap n, Homogeneous X m →
            (backwardOperator (D k) (J k) (w k) X).coeffNorm ≤
              (1 + (macroIndex k : ℝ)) ^ Cm *
                Real.exp (-c * Real.sqrt (s k) / (macroIndex k : ℝ) ^ 2) * X.coeffNorm

/-- Quantitative charging statements used by Y04, on the expanded components
actually generated by the logarithmic flag test, only on the positive
monotone clock tail. Full/prefix charging starts at u≥jBound. Unbounded
regular/good endpoints remain genuine outputs; no degree conclusion is a
premise of this predicate. -/
def BadCharging (Q : ℕ → ℝ) (jBound N Dstar : ℕ) (M hm b₀ : ℝ) : Prop :=
  let W := 2 * N + 1
  let alpha := M / (3 * (W : ℝ))
  MonotoneOn Q (Set.Ici jBound) ∧ (∀ j, jBound ≤ j → 0 < Q j) ∧
  (∀ u v, jBound ≤ u → FullBadComponent Q N M u v →
    alpha * (v - u : ℕ) ≤ Real.log (Q (v - N) / Q u) ∧
      (Dstar : ℝ) ^ (v - u) * Q u ≤ (b₀ / 2) * Q (v - N)) ∧
  (∀ u j, jBound ≤ u → u ≤ j → (u = 0 ∨ Regular Q N M (u - 1)) →
    (∀ r, u ≤ r → r < j → Bad Q N M r) →
    alpha * (j - u - W : ℕ) ≤ Real.log (Q j / Q u) ∧
      (Dstar : ℝ) ^ (j - u) * Q u ≤ (Dstar : ℝ) ^ W * Q j) ∧
  (¬ ∃ u, InfiniteBadComponent Q N M u) ∧
  (∀ J, ∃ j, max J jBound ≤ j ∧ Regular Q N M j) ∧
  ∀ J, ∃ j, max J jBound ≤ j ∧ Q j ≤ 3 * Real.exp hm * macroClock hm j

/-- Full Y04 quantifier order. `Cd` and `Dstar` depend only on dimension and
jet order: they precede *all* geometric and grid data. After choosing the flag
threshold, every sufficiently late regular endpoint initializes the same
construction. The original macro indices are retained. -/
def Y04 : Prop :=
  ∀ n d : ℕ, 2 ≤ d → ∃ (Cd : ℝ) (Dstar : ℕ), 0 < Cd ∧ 1 ≤ Dstar ∧
    ∀ (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
      (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector n → Pt X)
      (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (f : ℝ → Pt X → ComplexVector n),
      FlowStage X o h U P ρ → RicciWindows X o h ρ → JointPositiveClock X h →
      ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f →
      ∃ (time : ℝ → ℝ) (s₀ a₀ b₀ : ℝ), ClockParameter X o h ρ time s₀ ∧
        0 < a₀ ∧ a₀ < 1 ∧ 0 < b₀ ∧ ClockRateInput o h time s₀ a₀ b₀ ∧
        ∀ hm : ℝ, 0 < hm → hm < 1 → ∃ (N : ℕ) (M : ℝ),
          1 ≤ N ∧ Real.exp (-hm * N) ≤ a₀ ∧ 0 < M ∧
          Real.log (Dstar : ℝ) + max 0 (Real.log (2 / b₀)) / (2 * N + 1 : ℝ) ≤
            M / (3 * (2 * N + 1 : ℝ)) ∧ hm < M / (3 * (2 * N + 1 : ℝ)) ∧
          let Q := sampledSpeed o h time hm
          ∃ jBound : ℕ, N < jBound ∧ s₀ ≤ macroClock hm (jBound - N) ∧
            BadCharging Q jBound N Dstar M hm b₀ ∧
            ∃ scale K eps b : ℝ, 0 < scale ∧ 0 < K ∧ 0 < eps ∧
              eps < 1 / (10 * (n + 1 : ℝ)) ∧ 0 < b ∧
              ∃ jLate : ℕ, max N jBound < jLate ∧
                ∀ j₀ : ℕ, jLate ≤ j₀ → Regular Q N M j₀ →
                  let s := gridClock Q N M hm j₀
                  let tk := fun k => time (s k)
                  GridLayout Q N M hm j₀ ∧ (∀ k, s₀ ≤ s k ∧ t₀ ≤ tk k) ∧
                  ∃ (H Hinv G Ginv g : ℕ → PolyMap n) (E : Frames n) (L : Changes n),
                    PolynomialModels X o ρ F d hm Cd Dstar tk H Hinv G Ginv ∧
                    WindowRateBounds Q N M hm b₀ j₀ (rate F tk E) ∧
                    WeightEstimates Q N M hm scale K eps b j₀ (rate F tk E) ∧
                    RegularModelCompatibility F tk Q N M hm scale K eps j₀ Dstar E L H G Ginv g ∧
                    (∃ B : ℝ, 0 < B ∧ ∀ j, j₀ ≤ j →
                      ((forwardComp G (offset Q N M hm j₀ j)).degree : ℝ) ≤ B * Q j) ∧
                    ForwardDegreeControl G s hm

end Yau.Blueprint.Alignment
