import Yau.Blueprint.Convergence
import Yau.Blueprint.NormalizationTargets

/-!
# Concrete node contracts (planning only)

Each `def Xnn : Prop` is a mathematical obligation, not a proof or assumption.
Missing source IDs remain explicitly blocked in the source ledger. Local-domain
and existence corollaries are labelled; they do not close the full source lemma.
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section

namespace Yau.Blueprint

open Yau

variable {n : ℕ}

/-! ## Additional node predicates -/

/-- Distance structure used by all compactness arguments. -/
def DistanceStructure (X : KahlerManifold n) : Prop :=
  let d := lengthEDist X.metric.form
  (∀ x y, d x y ≠ ⊤) ∧ (∀ x y, d x y = 0 ↔ x = y) ∧ (∀ x y, d x y = d y x) ∧
  (∀ x y z, d x z ≤ d x y + d y z) ∧
  (∀ (x : Pt X) (s : Set (Pt X)), s ∈ 𝓝 x ↔ ∃ ε : ENNReal, 0 < ε ∧ {y | d x y < ε} ⊆ s) ∧
  (∀ (o : Pt X) (L : ℝ), IsCompact {x | d o x ≤ ENNReal.ofReal L})

/-- `lem:symplectic-evolution` (`discs.tex:90-102`), in induced cotangent coordinates. -/
def SymplecticEvolution {M : ComplexManifold n} (h : ℝ → HermitianField M) : Prop :=
  ∀ (x : M.Carrier) (z ξ : ComplexVector n) (t : ℝ), z ∈ chartTarget x → 0 < t →
    HasDerivAt (fun s => dualNormChart (h s) x z ξ)
      (symplecticP (leviMatrix (fun q : ComplexVector n × ComplexVector n =>
        dualNormChart (h t) x q.1 q.2) (z, ξ) cotangentDir)) t ∧
    ∀ d : M.Carrier → ℝ, SmoothFn d →
      symplecticP (leviMatrix (fun q : ComplexVector n × ComplexVector n =>
          dualNormChart (h t) x q.1 q.2 + inChart x d q.1) (z, ξ) cotangentDir) =
        deriv (fun s => dualNormChart (h s) x z ξ) t + traceWith (hMat (h t) x z) (leviC (inChart x d) z)

/-- `prop:disc-compactness` (`discs.tex:131-146`), for discs in `M` and in `Y = T^{*(1,0)}M`. -/
def DiscCompactness (X : KahlerManifold n) : Prop :=
  let g := X.metric.form
  ∀ K : Set (Pt X), IsCompact K → ∀ A₀ : ℝ,
    (∃ K' : Set (Pt X), IsCompact K' ∧ ∀ f : ℂ → Pt X, IsHolomorphicDisc f →
      (∀ ζ : ℂ, ‖ζ‖ = 1 → f ζ ∈ K) → discArea g f ≤ ENNReal.ofReal A₀ →
      ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → f ζ ∈ K') ∧
    (∀ fs : ℕ → ℂ → Pt X, (∀ k, IsHolomorphicDisc (fs k) ∧ (∀ ζ : ℂ, ‖ζ‖ = 1 → fs k ζ ∈ K) ∧
        discArea g (fs k) ≤ ENNReal.ofReal A₀) →
      ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → Pt X,
        MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (Metric.ball 0 1) ∧
        ∀ L ⊆ Metric.ball (0 : ℂ) 1, IsCompact L → ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ k, N ≤ k →
          ∀ ζ ∈ L, lengthEDist g (fs (φ k) ζ) (f ζ) < ε) ∧
    ∀ R : ℝ,
      (∃ K' : Set (Pt X), ∃ R' : ℝ, IsCompact K' ∧ ∀ (f : ℂ → Pt X) (ξ : ℂ → Covector n),
        IsCotangentDisc f ξ → (∀ ζ : ℂ, ‖ζ‖ = 1 → InCotangentCompact g K R (f ζ) (ξ ζ)) →
        discArea g f ≤ ENNReal.ofReal A₀ →
        ∀ ζ : ℂ, ‖ζ‖ ≤ 1 → InCotangentCompact g K' R' (f ζ) (ξ ζ)) ∧
      (∀ (fs : ℕ → ℂ → Pt X) (ξs : ℕ → ℂ → Covector n),
        (∀ k, IsCotangentDisc (fs k) (ξs k) ∧
          (∀ ζ : ℂ, ‖ζ‖ = 1 → InCotangentCompact g K R (fs k ζ) (ξs k ζ)) ∧
          discArea g (fs k) ≤ ENNReal.ofReal A₀) →
        ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ (f : ℂ → Pt X) (ξ : ℂ → Covector n),
          MDifferentiableOn 𝓘(ℂ, ℂ) (ComplexModel n) f (Metric.ball 0 1) ∧
          (∀ L ⊆ Metric.ball (0 : ℂ) 1, IsCompact L → ∀ ε : ENNReal, 0 < ε → ∃ N, ∀ k, N ≤ k →
            ∀ ζ ∈ L, lengthEDist g (fs (φ k) ζ) (f ζ) < ε) ∧
          ∀ ζ₀ ∈ Metric.ball (0 : ℂ) 1, ∃ V ∈ 𝓝 ζ₀,
            DifferentiableOn ℂ (fun ζ => covectorCoords (f ζ₀) (f ζ) (ξ ζ)) V ∧
            TendstoUniformlyOn (fun k ζ => covectorCoords (f ζ₀) (fs (φ k) ζ) (ξs (φ k) ζ))
              (fun ζ => covectorCoords (f ζ₀) (f ζ) (ξ ζ)) atTop V)

/-- Plurisubharmonic functions on an open subset of `ℂᵐ`. -/
def IsPshOn {m : ℕ} (u : ComplexVector m → EReal) (Ω : Set (ComplexVector m)) : Prop :=
  (∀ z ∈ Ω, u z < ⊤) ∧ UpperSemicontinuousOn u Ω ∧
    ∀ z w : ComplexVector m, (∀ ζ : ℂ, ‖ζ‖ ≤ 1 → z + ζ • w ∈ Ω) →
      ∀ φ : ℝ → ℝ, Continuous φ →
        (∀ θ : ℝ, u (z + Complex.exp (θ * Complex.I) • w) ≤ (φ θ : EReal)) →
        u z ≤ (circleAverage φ : EReal)

/-- `|a - b|` for extended reals, `⊤` across an infinite value. -/
def erealDist (a b : EReal) : ENNReal :=
  if a = b then 0 else if a = ⊥ ∨ a = ⊤ ∨ b = ⊥ ∨ b = ⊤ then ⊤ else ENNReal.ofReal |a.toReal - b.toReal|

/-- Local uniform collapse to minus infinity, tested on compact subsets. -/
def PshCollapses {m : ℕ} (D : Set (ComplexVector m))
    (us : ℕ → ComplexVector m → EReal) (phi : ℕ → ℕ) : Prop :=
  ∀ K ⊆ D, IsCompact K → ∀ A : ℝ, ∃ J, ∀ j, J ≤ j →
    ∀ z ∈ K, us (phi j) z ≤ ((-A : ℝ) : EReal)

/-- The noncollapsing alternative is an actual locally integrable psh limit. -/
def PshL1Limit {m : ℕ} (D : Set (ComplexVector m))
    (us : ℕ → ComplexVector m → EReal) (phi : ℕ → ℕ) : Prop :=
  ∃ u : ComplexVector m → EReal, IsPshOn u D ∧
    (∃ z ∈ D, u z ≠ ⊥) ∧
    (∀ᵐ z ∂(lebesgueC m).restrict D, u z ≠ ⊥) ∧
    (∀ K ⊆ D, IsCompact K → IntegrableOn (fun z => (u z).toReal) K (lebesgueC m) ∧
      Tendsto (fun j => ∫⁻ z in K, erealDist (us (phi j) z) (u z) ∂lebesgueC m) atTop (nhds 0)) ∧
    ∀ c : ℝ, (∀ z ∈ D, u z = c) → ∀ K ⊆ D, IsCompact K → ∀ ε, 0 < ε →
      ∃ J, ∀ j, J ≤ j → ∀ z ∈ K, us (phi j) z ≤ ((c + ε : ℝ) : EReal)

/-- The coordinate-domain compactness theorem and both lower-anchor clauses;
discs.tex:257-274. The extension from domains to arbitrary complex manifolds
is an explicit remaining atlas/splice obligation, not a claim made here. -/
def PshCompactnessBridge (m : ℕ) : Prop :=
  ∀ (D : Set (ComplexVector m)), IsOpen D → IsConnected D →
  ∀ (Ωs : ℕ → Set (ComplexVector m)) (us : ℕ → ComplexVector m → EReal),
    (∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1) ∧ Ωs j ⊆ D) → (⋃ j, Ωs j) = D →
    (∀ j, IsPshOn (us j) (Ωs j)) →
    (∀ K ⊆ D, IsCompact K → ∃ C : ℝ, ∀ j, K ⊆ Ωs j → ∀ z ∈ K, us j z ≤ C) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (PshCollapses D us phi ∨ PshL1Limit D us phi) ∧
      (∀ (K : Set (ComplexVector m)) (z : ℕ → ComplexVector m) (A : ℝ),
        IsCompact K → K ⊆ D → (∀ j, z j ∈ K ∧ z j ∈ Ωs (phi j) ∧
          ((-A : ℝ) : EReal) ≤ us (phi j) (z j)) → ¬ PshCollapses D us phi) ∧
      (∀ (K : Set (ComplexVector m)) (Es : ℕ → Set (ComplexVector m)) (A c : ℝ),
        IsCompact K → K ⊆ D → 0 < c →
        (∀ j, MeasurableSet (Es j) ∧ Es j ⊆ K ∩ Ωs (phi j) ∧
          ENNReal.ofReal c ≤ lebesgueC m (Es j) ∧
          ∀ z ∈ Es j, ((-A : ℝ) : EReal) ≤ us (phi j) z) → ¬ PshCollapses D us phi)

/-- Psh on an open manifold domain, through actual induced holomorphic charts. -/
def PshOnManifold {M : ComplexManifold n} (u : M.Carrier → EReal)
    (Ω : Set M.Carrier) : Prop :=
  (∀ x ∈ Ω, u x < ⊤) ∧ UpperSemicontinuousOn u Ω ∧
    ∀ x : M.Carrier,
      IsPshOn (fun z => u (chartInv x z))
        {z | z ∈ chartTarget x ∧ chartInv x z ∈ Ω}

/-- Uniform upper collapse on every fixed manifold compact. -/
def ManifoldPshCollapse {M : ComplexManifold n} (us : ℕ → M.Carrier → EReal)
    (phi : ℕ → ℕ) : Prop :=
  ∀ K : Set M.Carrier, IsCompact K → ∀ A : ℝ, ∃ J, ∀ j, J ≤ j →
    ∀ x ∈ K, us (phi j) x ≤ ((-A : ℝ) : EReal)

/-- The complete manifold version of discs.tex:257–274. A Riemannian volume is
fixed from a smooth positive metric, not replaced by an arbitrary measure.
No curvature or completeness premise is added to this compactness theorem. -/
def ManifoldPshCompactnessBridge (M : ComplexManifold n)
    (μ : Measure M.Carrier) : Prop :=
  ∀ (Ωs : ℕ → Set M.Carrier) (us : ℕ → M.Carrier → EReal),
    (∀ j, IsOpen (Ωs j) ∧ Ωs j ⊆ Ωs (j + 1)) → (⋃ j, Ωs j) = Set.univ →
    (∀ j, PshOnManifold (us j) (Ωs j)) →
    (∀ K : Set M.Carrier, IsCompact K → ∃ C : ℝ, ∀ j,
      K ⊆ Ωs j → ∀ x ∈ K, us j x ≤ (C : EReal)) →
    ∃ phi : ℕ → ℕ, StrictMono phi ∧
      (ManifoldPshCollapse us phi ∨
        ∃ u : M.Carrier → EReal, IsPsh u ∧
          (∃ x, u x ≠ ⊥) ∧ (∀ᵐ x ∂μ, u x ≠ ⊥) ∧
          (∀ K : Set M.Carrier, IsCompact K →
            IntegrableOn (fun x => (u x).toReal) K μ ∧
            Tendsto (fun j => ∫⁻ x in K, erealDist (us (phi j) x) (u x) ∂μ)
              atTop (𝓝 0)) ∧
          (∀ c : ℝ, (∀ x, u x = c) → ∀ K : Set M.Carrier, IsCompact K →
            ∀ ε : ℝ, 0 < ε → ∃ J, ∀ j, J ≤ j →
              ∀ x ∈ K, us (phi j) x ≤ ((c + ε : ℝ) : EReal))) ∧
      (∀ (K : Set M.Carrier) (z : ℕ → M.Carrier) (A : ℝ), IsCompact K →
        (∀ j, z j ∈ K ∧ z j ∈ Ωs (phi j) ∧ ((-A : ℝ) : EReal) ≤ us (phi j) (z j)) →
        ¬ ManifoldPshCollapse us phi) ∧
      (∀ (K : Set M.Carrier) (Es : ℕ → Set M.Carrier) (A c : ℝ), IsCompact K → 0 < c →
        (∀ j, MeasurableSet (Es j) ∧ Es j ⊆ K ∩ Ωs (phi j) ∧
          ENNReal.ofReal c ≤ μ (Es j) ∧
          ∀ x ∈ Es j, ((-A : ℝ) : EReal) ≤ us (phi j) x) →
        ¬ ManifoldPshCollapse us phi)

/-- Frobenius norm squared. -/
def frobSq {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : ℝ := ∑ i, ∑ j, ‖A i j‖ ^ 2

/-- `D(a)²` of `discs.tex:486-492` for a `2π`-periodic matrix function of the angle. -/
def halfSobolevSq {r : ℕ} (a : ℝ → Matrix (Fin r) (Fin r) ℂ) : ENNReal :=
  ENNReal.ofReal ((2 * Real.pi) ^ 2)⁻¹ *
    ∫⁻ t in Set.Icc (0 : ℝ) (2 * Real.pi), ∫⁻ θ in Set.Icc (0 : ℝ) (2 * Real.pi),
      ENNReal.ofReal (frobSq (a (t + θ) - a t) / ‖Complex.exp (θ * Complex.I) - 1‖ ^ 2)

def onCircle {r : ℕ} (H : ℂ → Matrix (Fin r) (Fin r) ℂ) : ℝ → Matrix (Fin r) (Fin r) ℂ :=
  fun t => H (Complex.exp (t * Complex.I))

def matOpNormR {r : ℕ} (A : Matrix (Fin r) (Fin r) ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (n := Fin r) (𝕜 := ℂ) A‖

/-- `lem:boundary-factorization` (`discs.tex:531-545`). -/
def BoundaryFactorization (r : ℕ) : Prop :=
  ∀ (L : ℝ → Matrix (Fin r) (Fin r) ℂ) (m M : ℝ), 0 < m → m ≤ M →
    (∀ i j, ContDiff ℝ ∞ (fun t => L t i j)) → (∀ t, L (t + 2 * Real.pi) = L t) →
    (∀ t, (L t - (m : ℂ) • 1).PosSemidef ∧ ((M : ℂ) • 1 - L t).PosSemidef) →
    ∃ H Hinv : ℂ → Matrix (Fin r) (Fin r) ℂ,
      (∀ i j, DifferentiableOn ℂ (fun ζ => H ζ i j) (Metric.ball 0 1) ∧
        ContDiffOn ℝ ∞ (fun ζ => H ζ i j) (Metric.closedBall 0 1) ∧
        ContDiffOn ℝ ∞ (fun ζ => Hinv ζ i j) (Metric.closedBall 0 1)) ∧
      (∀ ζ ∈ Metric.closedBall (0 : ℂ) 1, H ζ * Hinv ζ = 1 ∧ Hinv ζ * H ζ = 1) ∧
      (∀ t, L t = (onCircle H t)ᴴ * onCircle H t) ∧
      (∀ ζ ∈ Metric.ball (0 : ℂ) 1, matOpNormR (H ζ) ≤ Real.sqrt M ∧
        matOpNormR (Hinv ζ) ≤ (Real.sqrt m)⁻¹) ∧
      halfSobolevSq (onCircle H) ≤ ENNReal.ofReal (M / (2 * m ^ 2)) * halfSobolevSq L ∧
      halfSobolevSq (onCircle Hinv) ≤ ENNReal.ofReal (1 / (2 * m ^ 3)) * halfSobolevSq L

/-- `prop:disc-inequality` (`variation.tex:10-27`): viscosity inequality for the envelope. -/
def EnvelopeInequality (X : KahlerManifold n) (h : Flow X) : Prop :=
  ∀ T, 0 < T → ∀ (x : Pt X) (z η : ComplexVector n) (s : ℝ), z ∈ chartTarget x → 0 < s → s < T →
    ∀ φ : ComplexVector n × ComplexVector n × ℝ → ℝ, ContDiffAt ℝ ∞ φ (z, η, s) →
      (φ (z, η, s) : EReal) = envelopeChart h T x (z, η, s) →
      (∀ᶠ p in 𝓝 (z, η, s), (φ p : EReal) ≤ envelopeChart h T x p) →
      let W := leviMatrix (fun q : ComplexVector n × ComplexVector n => φ (q.1, q.2, s)) (z, η)
        cotangentDir
      W.toBlocks₂₂.PosDef →
      ∃ K : Herm n, K.PosSemidef ∧ (K - schurComplement W).PosSemidef ∧
        (Matrix.trace (W.toBlocks₂₂ᵀ * K)).re ≤ deriv (fun s' => φ (z, η, s')) s

/-- `lem:symplectic-schur` (`variation.tex:818-829`). -/
def SymplecticSchur (n : ℕ) : Prop :=
  ∀ Hm W : Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) ℂ, Hm.PosDef → W.IsHermitian →
    (Hm - W).PosSemidef → W.toBlocks₂₂.PosDef →
    (schurComplement Hm).PosSemidef ∧ (schurComplement Hm - schurComplement W).PosSemidef ∧
      (Matrix.trace (W.toBlocks₂₂ᵀ * schurComplement Hm)).re ≤ symplecticP Hm

/-- Feasible fiber ellipsoids `ξ^* D ξ ≤ v(x, ξ, t)` (`ellipsoids.tex:28-34`). -/
def FeasibleEllipsoid (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) (D : Herm n) : Prop :=
  D.PosDef ∧ ∀ η : ComplexVector n,
    ((star (WithLp.ofLp η) ⬝ᵥ (D *ᵥ WithLp.ofLp η)).re : EReal) ≤ envelopeChart h T x (z, η, t)

/-- `𝓛 = log det B`, `B` the determinant maximizer (chart-`x` cotangent coordinates). -/
def ellipsoidLogDet (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X)
    (z : ComplexVector n) (t : ℝ) : ℝ :=
  Real.log (sSup {d : ℝ | ∃ D, FeasibleEllipsoid X h T x z t D ∧ d = D.det.re})

/-- `F₀ = log det b_t - 𝓛`, `b_t = h_t^{-T}`. -/
def volumeGap (X : KahlerManifold n) (h : Flow X) (T : ℝ) (x : Pt X) (z : ComplexVector n)
    (t : ℝ) : ℝ :=
  -logDet (h t) x z - ellipsoidLogDet X h T x z t

/-- `ell:optimizer-contacts` (`ellipsoids.tex:36-53`). -/
def OptimizerContacts (X : KahlerManifold n) (h : Flow X) (ρ : STF X) : Prop :=
  ∀ T, 0 < T → ∀ (x : Pt X),
    LowerSemicontinuousOn (fun p : ComplexVector n × ℝ => ellipsoidLogDet X h T x p.1 p.2)
      (chartTarget x ×ˢ Set.Ioo 0 T) ∧
    ∀ (z : ComplexVector n) (t : ℝ), z ∈ chartTarget x → t ∈ Set.Ioo 0 T →
      (∃! B : Herm n, FeasibleEllipsoid X h T x z t B ∧
        ∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) ∧
      0 ≤ volumeGap X h T x z t ∧ volumeGap X h T x z t ≤ ρ (chartInv x z) t ∧
      ∃ B : Herm n, FeasibleEllipsoid X h T x z t B ∧
        (∀ D, FeasibleEllipsoid X h T x z t D → D.det.re ≤ B.det.re) ∧
        ∀ ε, 0 < ε → ∃ (m : ℕ) (η : Fin m → ComplexVector n) (α : Fin m → ℝ),
          (∀ i, 0 < α i ∧ α i ≤ ε ∧ envelopeChart h T x (z, η i, t) = 1 ∧
            (star (WithLp.ofLp (η i)) ⬝ᵥ (B *ᵥ WithLp.ofLp (η i))).re = 1) ∧
          ∑ i, (α i : ℂ) • Matrix.vecMulVec (WithLp.ofLp (η i)) (star (WithLp.ofLp (η i))) = B⁻¹ ∧
          ∑ i, α i = n

/-- `prop:ellipsoid-comparison` (`ellipsoids.tex:106-115`): lower viscosity inequality. -/
def EllipsoidComparison (X : KahlerManifold n) (h : Flow X) : Prop :=
  ∀ T, 0 < T → ∀ (x : Pt X) (z : ComplexVector n) (t : ℝ), z ∈ chartTarget x → t ∈ Set.Ioo 0 T →
    ∀ testFn : ComplexVector n × ℝ → ℝ, ContDiffAt ℝ ∞ testFn (z, t) →
      testFn (z, t) = ellipsoidLogDet X h T x z t →
      (∀ᶠ p in 𝓝 (z, t), testFn p ≤ ellipsoidLogDet X h T x p.1 p.2) →
      Real.exp (-volumeGap X h T x z t) *
          traceWith (hMat (h t) x z) (leviC (fun w => testFn (w, t)) z) ≤
        deriv (fun t' => testFn (z, t')) t

/-- Directions of `(z, ξ, w) ∈ ℂⁿ × ℂⁿ × ℂ`. -/
def jointDir : (Fin n ⊕ Fin n) ⊕ Unit → ComplexVector n × ComplexVector n × ℂ :=
  Sum.elim (Sum.elim (fun i => (stdVec i, 0, 0)) (fun i => (0, stdVec i, 0))) (fun _ => (0, 0, 1))

/-- `thm:joint-positivity` (`ellipsoids.tex:460-468`). -/
def JointPositivity (X : KahlerManifold n) (h : Flow X) : Prop :=
  (∀ (x : Pt X) (z ξ : ComplexVector n) (w : ℂ), z ∈ chartTarget x →
    (leviMatrix (fun q : ComplexVector n × ComplexVector n × ℂ =>
      dualNormChart (h (Real.exp (2 * q.2.2.re))) x q.1 q.2.1) (z, ξ, w) jointDir).PosSemidef) ∧
  ∀ T, 0 < T → ∀ (x : Pt X) (ξ : Covector n) (s : ℝ), 0 < s → s < T →
    envelope h T x ξ s = (dualNorm (h s) x ξ : EReal)

/-- `prop:harnack-completeness` (`charts.tex:24-45`). -/
def HarnackCompleteness (X : KahlerManifold n) (o : Pt X) (h : Flow X) : Prop :=
  (∀ t, 0 ≤ t → NonnegBisectional (h t)) ∧ (∀ t, 0 < t → IsCompleteDistance (lengthDist (h t))) ∧
  (∀ t, 0 ≤ t → ∀ x, (ricci (h t) x).PosDef) ∧
  (∀ (x : Pt X) (t : ℝ), 0 < t →
    (Matrix.of (fun a b => deriv (fun s => ricci (h s) x a b) t) +
      ricci (h t) x * (gMat (h t) x)⁻¹ * ricci (h t) x + ((t⁻¹ : ℝ) : ℂ) • ricci (h t) x).PosSemidef) ∧
  (∀ (x : Pt X) (t : ℝ), 0 < t → ∀ V : ComplexVector n,
    0 ≤ deriv (fun s => scalarCurvature (h s) x) t + t⁻¹ * scalarCurvature (h t) x +
      2 * (∑ i, V i * wirt (fun z => Complex.ofReal (inChart x (scalarCurvature (h t)) z)) (chartPt x x)
        (stdVec i)).re +
      (star (WithLp.ofLp V) ⬝ᵥ (ricci (h t) x *ᵥ WithLp.ofLp V)).re) ∧
  (∀ x t t', 0 ≤ t → t ≤ t' → HermLE (gMat (h t') x) (gMat (h t) x)) ∧
  (∃ C : ℝ, ∀ t, 0 ≤ t → scalarCurvature (h t) o ≤ C) ∧
  (∃ C : ℝ, ∀ x y t t', 0 < t → t < t' →
    scalarCurvature (h t) x ≤ scalarCurvature (h t') y * (t' / t) *
      Real.exp (C * distFrom (h t) x y ^ 2 / (t' - t))) ∧
  (∀ K : Set (Pt X), IsCompact K → ∃ CK aK : ℝ, 0 < aK ∧ ∀ t, 1 ≤ t → ∀ x ∈ K,
    HermLE (gMat (h t) x) (((CK * t ^ (-aK) : ℝ) : ℂ) • gMat X.metric.form x))

/-- `chart:local-charts` (`charts.tex:161-175`). -/
def UniformCharts (X : KahlerManifold n) (h : Flow X) : Prop :=
  ∀ K : Set (Pt X), IsCompact K → ∃ r c C t₀ : ℝ, 0 < r ∧ 0 < c ∧ 0 < C ∧ ∃ Cm : ℕ → ℝ → ℝ,
    ∀ t, t₀ ≤ t → ∀ p ∈ K, ∃ Φ, UnitaryChart (h t) p Φ r c C ∧
      ∀ (m : ℕ) (r' : ℝ), 0 < r' → r' < r → PullbackDerivBound (h t) Φ r' m (Cm m r')

/-- Greatest eigenvalue of `A` relative to `H`. -/
def relMaxEigenvalue (H A : Herm n) : ℝ :=
  ⨆ v : {v : ComplexVector n // v ≠ 0},
    (star (WithLp.ofLp v.1) ⬝ᵥ (A *ᵥ WithLp.ofLp v.1)).re /
      (star (WithLp.ofLp v.1) ⬝ᵥ (H *ᵥ WithLp.ofLp v.1)).re

/-- `lem:static-distortion` (`charts.tex:308-321`); `A, B` are the least and greatest singular
lengths of `dΦ(0)` (Euclidean domain, `g` target). -/
def StaticDistortion (X : KahlerManifold n) : Prop :=
  ∀ r c : ℝ, 0 < r → 0 < c → ∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, 0 < C ∧
    ∀ Φ : ComplexVector n → Pt X, IsLocalBiholomorphism Φ r → Φ 0 ∈ K →
      (∀ z ∈ Metric.ball (0 : ComplexVector n) r,
        HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat X.metric.form Φ z)) →
      Real.sqrt (relMaxEigenvalue 1 (pullbackMat X.metric.form Φ 0)) ≤
        C * (1 + Real.sqrt (relMinEigenvalue 1 (pullbackMat X.metric.form Φ 0))) ^ C

/-- `chart:psh-liouville` (`charts.tex:825-828`). -/
def PshLiouville (X : KahlerManifold n) : Prop :=
  ∀ u : Pt X → EReal, IsPsh u → (∃ C : ℝ, ∀ x, u x ≤ (C : EReal)) → ∀ x y, u x = u y

/-- `lem:volume-jets` (`dynamics.tex:146-153`). -/
def VolumeJets (n d : ℕ) : Prop :=
  ∃ (Dd : ℕ) (C : ℝ), ∀ J : PolyMap n, IsConstantVolumeJet J d →
    ∃ G Ginv : PolyMap n, IsPolyAutomorphism G Ginv ∧ PolyMap.JetEq G J d ∧
      G.degree ≤ Dd ∧ Ginv.degree ≤ Dd ∧
      G.coeffNorm + Ginv.coeffNorm ≤ C * (1 + J.coeffNorm + matOpNorm J.linearPart⁻¹) ^ C

/-! ## Node contracts -/

/-- Full real/Chern tensor, normalized HBC, Ricci and scalar convention goals. -/
def G01 : Prop := PaperCurvatureNormalizationTarget

/-- Remaining metric, form/Hodge and real-flow normalization obligations. -/
def G04 : Prop := PaperMetricNormalizationTarget ∧
  PaperHodgeNormalizationTarget ∧ PaperFlowNormalizationTarget

/-- G02: the Riemannian volume exists and is unique. -/
def G02 : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n) (h : HermitianField M), MetricSmooth h →
    ∃! μ : Measure M.Carrier, IsRiemannianVolume h μ

/-- G03: length distance, topology and Hopf–Rinow properness. -/
def G03 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), DistanceStructure X

def P02 : Prop := ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X), StrictPshWeight X o
def P03 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), FiniteInterpolation X
def P04 : Prop := ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X), CanonicalInitialData X o
def P07 : Prop := ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X), ∃ u, ControlledExhaustion X o u
def P08 : Prop := ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X), CanonicalAverages X o

def P01 : Prop := ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X), BusemannConclusion X o
def P05 : Prop := ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X), CanonicalWeightedGrowth X o

def F01 : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X), ∃ (h : Flow X) (U P ρ : STF X), LocalizedFlow X o h U P ρ

def F04 : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ → ScalarComparison X h ρ

def D01 : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n) (g : HermitianField M) (h : ℝ → HermitianField M),
    IsKahlerRicciFlow g h → SymplecticEvolution h

def D02 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), DiscCompactness X

def D04 : Prop := ∀ (n : ℕ) (M : ComplexManifold n) (g : HermitianField M),
  MetricSmooth g → ∀ μ, IsRiemannianVolume g μ → ManifoldPshCompactnessBridge M μ

def D06 : Prop := ∀ r : ℕ, BoundaryFactorization r

/-- Shape of every node stated for the flow of Theorem 3.1. -/
def ForFlow (C : ∀ {n : ℕ} (X : KahlerManifold n), Pt X → Flow X → STF X → Prop) : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ → C X o h ρ

def F02 : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ → MetricDefectAverages X o h

def F03 : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ → IntegrableCutoffs X o h

def F05 : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    LocalizedFlow X o h U P ρ → SmoothMajorant X h ρ

def V01 : Prop := ForFlow fun X _ h _ => EnvelopeInequality X h
def V05 : Prop := ∀ n : ℕ, SymplecticSchur n
def E01 : Prop := ForFlow fun X _ h ρ => OptimizerContacts X h ρ
def E02 : Prop := ForFlow fun X _ h _ => EllipsoidComparison X h
def E03 : Prop := ForFlow fun X _ h _ => JointPositivity X h
def C01 : Prop := ForFlow fun X o h _ => HarnackCompleteness X o h
def C02 : Prop := ForFlow fun X _ h _ => UniformCharts X h
def C03 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), StaticDistortion X
def C04 : Prop := ForFlow fun X o h ρ => RicciWindows X o h ρ
def C05 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), SimplyConnectedSpace (Pt X)

/-- Concrete inlet used by the simple-connectivity argument, on the
original manifold and precisely the flow supplied by F01. No topology
conclusion or limiting/concavity/contraction output is assumed here. -/
def C05SourceInputs (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) : Prop :=
  FlowStage X o h U P ρ ∧ HarnackCompleteness X o h ∧ RicciWindows X o h ρ

/-- Auxiliary producer target for C05's inlet, not an added premise of C05.
F01,F04,C01,C04 are instantiated at the same witnesses to construct it. -/
def C05InputProducer : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X),
    ∃ (h : Flow X) (U P ρ : STF X), C05SourceInputs X o h U P ρ
def C06 : Prop := ∀ (n : ℕ) (X : KahlerManifold n), PshLiouville X

def C07 : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X),
    FlowStage X o h U P ρ → ∃ (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector n → Pt X)
      (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (f : ℝ → Pt X → ComplexVector n),
      ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f

def Y02 : Prop := ∀ n d : ℕ, 2 ≤ d → VolumeJets n d

def U01 : Prop := ∀ n m : ℕ, BackwardShadowing n m

def U02 : Prop :=
  ∀ (n : ℕ) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector n → Pt X)
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (f : ℝ → Pt X → ComplexVector n),
    FlowStage X o h U P ρ → RicciWindows X o h ρ → ShrinkingCharts X o h ρ r₀ r₁ σ C Cb t₀ Φ F f →
    ∃ (d : ℕ) (σ' γ' : ℝ), 2 ≤ d ∧ 0 < γ' ∧ γ' < σ' / 2 ∧ σ' ≤ σ ∧
      ∀ Cd Dg : ℝ, ∃ h₀ : ℝ, 0 < h₀ ∧ h₀ ≤ 1 ∧ ∀ hm : ℝ, 0 < hm → hm < h₀ →
        ∀ (tk : ℕ → ℝ) (H Hinv G Ginv : ℕ → PolyMap n),
          PolynomialModels X o ρ F d hm Cd Dg tk H Hinv G Ginv →
          (∀ᶠ k in atTop, 0 ≤ tk k) →
          ∃ (Ψ : Pt X → ComplexVector n) (Ψinv : ComplexVector n → Pt X)
            (global : Uniformization.OpenCoordinateData n X.manifold),
            GlobalCoordinates X o ρ f tk H G Ginv σ' γ' Ψ Ψinv ∧
              global.map = Ψ ∧ global.inverse_extension = Ψinv ∧
              ImageDynamics global G Ginv (fun k => ρ o (tk k)) σ' γ'

def U03 {n : ℕ} {M : ComplexManifold n}
    (global : Uniformization.OpenCoordinateData n M)
    (G Ginv : ℕ → PolyMap n) (s : ℕ → ℝ) (sigma gamma hm : ℝ) : Prop :=
  ImageDynamics global G Ginv s sigma gamma →
    ForwardDegreeControl G s hm → Nonempty (U03Output global)

def U04 {n : ℕ} {M : ComplexManifold n}
    (global : Uniformization.OpenCoordinateData n M) (out : U03Output global) : Prop :=
  let result := global.toGlobal out.1
  result.manifold = M ∧ BiholomorphicToComplexEuclidean result.manifold

/-- Closed goal for U03. The parameterized `U03` API remains available, but
the producer premise in an assembly task quantifies over every actual map,
model sequence and clock returned by U02/Y04. -/
def U03Goal : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n)
    (global : Uniformization.OpenCoordinateData n M)
    (G Ginv : ℕ → PolyMap n) (s : ℕ → ℝ) (sigma gamma hm : ℝ),
    U03 global G Ginv s sigma gamma hm

/-- Closed goal for packaging the exact map and its own U03 witness. -/
def U04Goal : Prop :=
  ∀ (n : ℕ) (M : ComplexManifold n)
    (global : Uniformization.OpenCoordinateData n M) (out : U03Output global),
    U04 global out

/-- U05: the existential splice in uniformization.tex:341-347,376-377.
For each original paper manifold, the upstream flow/chart/model producers
must supply an actual coordinate map and the surjectivity witness for that
same map. This is an open conditional assembly target, not assumed data. -/
def U05 : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ X : KahlerManifold n,
    ∃ global : Uniformization.OpenCoordinateData n X.manifold,
      Nonempty (U03Output global)

/-- END: Theorem 1.1, identical to `Yau.main` in `spec/STATEMENT.lean`. -/
def END : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ X : KahlerManifold n, BiholomorphicToComplexEuclidean X.manifold

end Yau.Blueprint
