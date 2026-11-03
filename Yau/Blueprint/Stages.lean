import Yau.Geometry.Calculus
import Yau.Geometry.Polynomial
import Yau.Uniformization.Boundary

/-!
# Stage predicates of the proof of Theorem 1.1

The predicates give explicit formulas on concrete data (metric families,
space-time functions, charts and polynomial maps). The local polynomial-model
predicate deliberately separates the forward-degree output, and local-domain
versions are labelled where infrastructure is still missing. Data are
arguments or existentially quantified in a node contract; no predicate is a structure field.
Node contracts (`Yau/Blueprint/Nodes.lean`) quantify over these data.

Indexing convention: the paper's volume clock is `s = ρ(o,t)`; objects the paper indexes by a
late clock value `s` are indexed here by the corresponding time `t` (the clock is a strictly
increasing change of variable for late times, `C04`).
-/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

noncomputable section

namespace Yau.Blueprint

open Yau

variable {n : ℕ}

abbrev Pt (X : KahlerManifold n) := X.manifold.Carrier
abbrev Flow (X : KahlerManifold n) := ℝ → HermitianField X.manifold
/-- Real functions on space-time `M × ℝ`. -/
abbrev STF (X : KahlerManifold n) := Pt X → ℝ → ℝ
abbrev Herm (n : ℕ) := Matrix (Fin n) (Fin n) ℂ

/-- Loewner order of Hermitian forms (paper column convention). -/
def HermLE (A B : Herm n) : Prop := (B - A).PosSemidef

/-- `(∂_t - Δ_{h_t}) f` with the time derivative taken within `I`. -/
def heatOp {X : KahlerManifold n} (h : Flow X) (I : Set ℝ) (f : STF X) (x : Pt X) (t : ℝ) : ℝ :=
  derivWithin (f x) I t - laplacian (h t) (fun y => f y t) x

/-! ## `thm:localized-flow` (`flow.tex:8-34`) -/

def LocalizedFlow (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X) : Prop :=
  IsKahlerRicciFlow X.metric.form h ∧
  SmoothSpaceTime U (Set.Ici 0) ∧ SmoothSpaceTime P (Set.Ici 0) ∧ SmoothSpaceTime ρ (Set.Ici 0) ∧
  (∀ t, 0 ≤ t → ∀ x, HermLE (gMat (h t) x) (gMat X.metric.form x)) ∧
  (∀ t, 0 ≤ t → ∀ x,
    gMat (h t) x = gMat X.metric.form x - (t : ℂ) • ricci X.metric.form x + levi (fun y => U y t) x) ∧
  (∀ x, U x 0 = 0) ∧
  (∀ x t, 0 ≤ t → HasDerivWithinAt (U x) (P x t) (Set.Ici 0) t) ∧
  (∀ x t, 0 ≤ t → P x t = Real.log ((gMat (h t) x).det.re / (gMat X.metric.form x).det.re)) ∧
  (∀ x t, 0 ≤ t → ρ x t = -P x t ∧ 0 ≤ ρ x t) ∧
  (∀ x t, 0 ≤ t → HasDerivWithinAt (P x) (-scalarCurvature (h t) x) (Set.Ici 0) t ∧
    0 ≤ scalarCurvature (h t) x) ∧
  (∀ T, 0 ≤ T → ∃ C : ℝ, ∀ μ, IsRiemannianVolume X.metric.form μ → ∀ L, 1 ≤ L →
    ∀ t ∈ Set.Icc 0 T, BallIntegralLE X.metric.form μ o (fun x => ρ x t) L (C * L)) ∧
  (∀ x, ∃ C : ℝ, ∀ t, 0 ≤ t → ρ x t ≤ C * (1 + t)) ∧
  (∀ T, 0 < T → ∃ Q : STF X, ∃ c : ℝ, 0 < c ∧ SmoothSpaceTime Q (Set.Icc 0 T) ∧
    ∀ x t, t ∈ Set.Icc 0 T → 0 < Q x t ∧ c * (1 + distFrom X.metric.form o x ^ 2) ≤ Q x t ∧
      c * traceWith (gMat (h t) x) (gMat X.metric.form x) ≤ heatOp h (Set.Icc 0 T) Q x t)

/-! ## `prop:scalar-comparison` (`flow.tex:527-557`) -/

def ScalarComparison (X : KahlerManifold n) (h : Flow X) (ρ : STF X) : Prop :=
  ∀ T, 0 < T →
    -- (i) `ρ` solves the source equation and is the minimal nonnegative solution
    (∀ x t, t ∈ Set.Icc 0 T →
      heatOp h (Set.Icc 0 T) ρ x t = traceWith (gMat (h t) x) (ricci X.metric.form x)) ∧
    (∀ ρ' : STF X, SmoothSpaceTime ρ' (Set.Icc 0 T) → (∀ x t, t ∈ Set.Icc 0 T → 0 ≤ ρ' x t) →
      (∀ x, ρ' x 0 = 0) →
      (∀ x t, t ∈ Set.Icc 0 T →
        heatOp h (Set.Icc 0 T) ρ' x t = traceWith (gMat (h t) x) (ricci X.metric.form x)) →
      ∀ x t, t ∈ Set.Icc 0 T → ρ x t ≤ ρ' x t) ∧
    -- (i) supercaloric tails `ρ_j`
    (∃ ρs : ℕ → STF X, ∃ Cs : ℕ → ℝ,
      (∀ j, SmoothSpaceTime (ρs j) (Set.Icc 0 T) ∧ ∀ x t, t ∈ Set.Icc 0 T →
        0 ≤ ρs j x t ∧ ρs j x t ≤ ρ x t ∧ ρ x t - Cs j ≤ ρs j x t ∧
        0 ≤ heatOp h (Set.Icc 0 T) (ρs j) x t) ∧
      ∀ K : Set (Pt X), IsCompact K → ∀ ε, 0 < ε → ∃ J, ∀ j, J ≤ j →
        ∀ x ∈ K, ∀ t ∈ Set.Icc 0 T, ρs j x t ≤ ε) ∧
    -- (ii) nonlinear comparison
    (∀ v : STF X,
      UpperSemicontinuousOn (fun p : Pt X × ℝ => v p.1 p.2) (Set.univ ×ˢ Set.Icc 0 T) →
      (∀ K : Set (Pt X), IsCompact K → ∃ C : ℝ, ∀ x ∈ K, ∀ t ∈ Set.Icc 0 T, |v x t| ≤ C) →
      (∀ x t, t ∈ Set.Icc 0 T → 0 ≤ v x t ∧ v x t ≤ ρ x t) →
      NonlinearViscositySub h T v →
      ∀ x t, t ∈ Set.Ico 0 T → v x t = 0)

/-- Everything later sections use about the flow: Theorem 3.1 and Proposition 3.x. -/
def FlowStage (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X) : Prop :=
  LocalizedFlow X o h U P ρ ∧ ScalarComparison X h ρ

/-! ## Volume clock (`charts.tex:510-560`) -/

/-- `q = ds/dτ = t R(o,t)` as a function of time. -/
def clockSpeed {X : KahlerManifold n} (o : Pt X) (h : Flow X) (t : ℝ) : ℝ :=
  t * scalarCurvature (h t) o

/-- `λ_min(t Ric(h_t))` at `o` relative to `h_t`. -/
def ricciMin {X : KahlerManifold n} (o : Pt X) (h : Flow X) (t : ℝ) : ℝ :=
  relMinEigenvalue (gMat (h t) o) ((t : ℂ) • ricci (h t) o)

/-- Positive multiple of a Hermitian metric. -/
def scaleField {M : ComplexManifold n} (c : ℝ) (hc : 0 < c) (k : HermitianField M) :
    HermitianField M := fun x =>
  { toFun := fun u v => (c : ℂ) * (k x).toFun u v
    map_add_left := by intro u₁ u₂ v; rw [(k x).map_add_left]; ring
    map_smul_left := by intro a u v; rw [(k x).map_smul_left]; ring
    map_add_right := by intro u v₁ v₂; rw [(k x).map_add_right]; ring
    map_smul_right := by intro a u v; rw [(k x).map_smul_right]; ring
    conjugate_symmetric := by
      intro u v
      simpa only [star_mul', Complex.star_def, Complex.conj_ofReal] using
        congrArg (fun z : ℂ => (c : ℂ) * z) ((k x).conjugate_symmetric u v)
    self_adjoint := by
      intro u
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, mul_zero,
        zero_mul, add_zero, (k x).self_adjoint]
    positive_definite := by
      intro u
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
      constructor
      · exact mul_nonneg hc.le ((k x).positive_definite u).1
      · rw [mul_eq_zero, or_iff_right (ne_of_gt hc)]
        exact ((k x).positive_definite u).2 }

/-- Pullback `Φ^*k` of a Hermitian metric by a map `Φ : ℂⁿ ⊇ B → M`, as a Gram matrix. -/
def pullbackMat {M : ComplexManifold n} (k : HermitianField M) (Φ : ComplexVector n → M.Carrier)
    (z : ComplexVector n) : Herm n :=
  fun a b => (k (Φ z)).toFun (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z (stdVec a))
    (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z (stdVec b))

/-- Holomorphic local biholomorphism `B_{ℂⁿ}(r) → M`. -/
def IsLocalBiholomorphism {M : ComplexManifold n} (Φ : ComplexVector n → M.Carrier) (r : ℝ) :
    Prop :=
  ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Φ (Metric.ball 0 r) ∧
    ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      Function.Bijective (mfderiv 𝓘(ℂ, ComplexVector n) (ComplexModel n) Φ z)

/-- Real derivative bounds up to order `m` of the pulled-back coefficients on `B(r)`. -/
def PullbackDerivBound {M : ComplexManifold n} (k : HermitianField M)
    (Φ : ComplexVector n → M.Carrier) (r : ℝ) (m : ℕ) (C : ℝ) : Prop :=
  ∀ j ≤ m, ∀ z ∈ Metric.ball (0 : ComplexVector n) r, ∀ a b : Fin n,
    ‖iteratedFDeriv ℝ j (fun w => pullbackMat k Φ w a b) z‖ ≤ C

/-- Uniformly controlled `k`-unitary chart of radius `r` centred at `p`. -/
def UnitaryChart {M : ComplexManifold n} (k : HermitianField M) (p : M.Carrier)
    (Φ : ComplexVector n → M.Carrier) (r c C : ℝ) : Prop :=
  IsLocalBiholomorphism Φ r ∧ Φ 0 = p ∧ pullbackMat k Φ 0 = 1 ∧
    ∀ z ∈ Metric.ball (0 : ComplexVector n) r,
      HermLE ((c : ℂ) • (1 : Herm n)) (pullbackMat k Φ z) ∧
      HermLE (pullbackMat k Φ z) ((C : ℂ) • (1 : Herm n))

/-- `prop:ricci-windows` (`charts.tex:528-560`), with clock `s(t) = ρ(o,t)`. -/
def RicciWindows (X : KahlerManifold n) (o : Pt X) (h : Flow X) (ρ : STF X) : Prop :=
  let s := fun t => ρ o t
  let q := clockSpeed o h
  (∃ t₁, 0 < t₁ ∧ StrictMonoOn s (Set.Ici t₁) ∧ MonotoneOn q (Set.Ici t₁) ∧
      ∀ t, t₁ ≤ t → HasDerivAt s (scalarCurvature (h t) o) t) ∧
  (∃ c, 0 < c ∧ ∃ t₂, ∀ t, t₂ ≤ t → c ≤ q t) ∧
  Tendsto s atTop atTop ∧
  (∃ C, ∀ t, 1 ≤ t → q t ≤ C * t) ∧
  (∀ ε, 0 < ε → ∀ T, ∃ t, T ≤ t ∧ q t ≤ (2 + ε) * s t) ∧
  (∀ K : Set (Pt X), IsCompact K → ∀ ε, 0 < ε → ∃ T, ∀ t, T ≤ t → ∀ x ∈ K,
      |ρ x t / s t - 1| ≤ ε) ∧
  (∀ K : Set (Pt X), IsCompact K → ∃ cK, 0 < cK ∧ ∃ T, ∀ t, T ≤ t → ∀ x ∈ K,
      HermLE ((Real.exp (-2 * s t) : ℂ) • gMat X.metric.form x) (gMat (h t) x) ∧
      HermLE (gMat (h t) x) ((Real.exp (-cK * s t) : ℂ) • gMat X.metric.form x)) ∧
  (∃ a₀ b₀, 0 < a₀ ∧ a₀ < 1 ∧ 0 < b₀ ∧
    (∃ T, ∀ t t', T ≤ t → 0 ≤ t' → s t' = a₀ * s t → b₀ * q t' ≤ ricciMin o h t) ∧
    ∃ S : ℕ → ℝ, ∃ K₀ : ℝ, Tendsto S atTop atTop ∧
    (∀ i t t', 0 ≤ t → 0 ≤ t' → s t = 2 * S i → s t' = a₀ * S i → q t ≤ K₀ * q t') ∧
    ∃ tw : ℕ → ℝ, (∀ i, 0 < tw i) ∧ Tendsto tw atTop atTop ∧
      (∀ i, 5 * S i / 4 ≤ s (tw i) ∧ s (tw i) ≤ 7 * S i / 4) ∧
      Tendsto (fun i => deriv q (tw i) / (q (tw i) * scalarCurvature (h (tw i)) o)) atTop (𝓝 0) ∧
      -- rescaled flows `g_i(z) = R_i h_{t_i + z/R_i}`, `R_i = R(o,t_i)`
      ∃ θ, 0 < θ ∧ ∃ lambda0, 0 < lambda0 ∧
        (∀ i, 0 < scalarCurvature (h (tw i)) o) ∧
        (∀ i (hR : 0 < scalarCurvature (h (tw i)) o),
          let R := scalarCurvature (h (tw i)) o
          let g0 := scaleField R hR (h (tw i))
          scalarCurvature g0 o = 1 ∧ lambda0 ≤ relMinEigenvalue (gMat g0 o) (ricci g0 o)) ∧
        ∀ r, 0 < r → ∃ rc c C : ℝ, 0 < rc ∧ 0 < c ∧ ∃ Cm : ℕ → ℝ, ∀ i
          (hR : 0 < scalarCurvature (h (tw i)) o),
          let R := scalarCurvature (h (tw i)) o
          ∀ p, p ∈ distBall (scaleField R hR (h (tw i))) o r → ∀ z, |z| < θ →
            0 ≤ tw i + z / R →
            ∃ Φ, UnitaryChart (scaleField R hR (h (tw i + z / R))) p Φ rc c C ∧
              ∀ m, PullbackDerivBound (scaleField R hR (h (tw i + z / R))) Φ (rc / 2) m (Cm m))

/-! ## `prop:shrinking-charts` (`charts.tex:882-923`), indexed by time -/

def ShrinkingCharts (X : KahlerManifold n) (o : Pt X) (h : Flow X) (ρ : STF X)
    (r₀ r₁ σ C Cb t₀ : ℝ) (Φ : ℝ → ComplexVector n → Pt X)
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (f : ℝ → Pt X → ComplexVector n) : Prop :=
  let s := fun t => ρ o t
  0 < r₁ ∧ r₁ < r₀ ∧ 0 < σ ∧ 0 < C ∧
  (∀ t, t₀ ≤ t → UnitaryChart (h t) o (Φ t) r₀ C⁻¹ C) ∧
  (∀ t t', t₀ ≤ t → t ≤ t' →
    DifferentiableOn ℂ (F t t') (Metric.ball 0 r₁) ∧
    (∀ z ∈ Metric.ball (0 : ComplexVector n) r₁,
      Function.Bijective (fderiv ℂ (F t t') z) ∧ ‖F t t' z‖ ≤ Cb) ∧
    F t t' 0 = 0 ∧ (∀ᶠ z in 𝓝 0, Φ t' (F t t' z) = Φ t z) ∧
    ‖fderiv ℂ (F t t') 0‖ ≤ 1 ∧
    ‖LinearMap.det (fderiv ℂ (F t t') 0 : ComplexVector n →ₗ[ℂ] ComplexVector n)‖ =
      Real.exp (-(s t' - s t) / 2) ∧
    ‖(fderiv ℂ (F t t') 0).inverse‖ ≤ Real.exp ((s t' - s t) / 2)) ∧
  (∀ t t' t'', t₀ ≤ t → t ≤ t' → t' ≤ t'' → ∀ᶠ z in 𝓝 0, F t' t'' (F t t' z) = F t t'' z) ∧
  (∀ t, t₀ ≤ t → f t o = 0) ∧
  (∀ K : Set (Pt X), IsCompact K → ∃ TK, t₀ ≤ TK ∧ ∀ t, TK ≤ t → ∃ V : Set (Pt X), IsOpen V ∧ K ⊆ V ∧
    MDifferentiableOn (ComplexModel n) 𝓘(ℂ, ComplexVector n) (f t) V ∧
    ∀ x ∈ V, f t x ∈ Metric.ball 0 r₀ ∧ Φ t (f t x) = x ∧
      ∀ t', t ≤ t' → f t x ∈ Metric.ball 0 r₁ → f t' x = F t t' (f t x)) ∧
  (∀ K : Set (Pt X), IsCompact K → ∃ TK, ∀ t, TK ≤ t → ∀ x ∈ K,
    ‖f t x‖ ≤ Real.exp (-σ * s t)) ∧
  (∀ d : ℕ, ∃ Cd Td, ∀ t t', Td ≤ t → t ≤ t' →
    jetNorm (F t t') d ≤ Cd * min 1 (Real.exp (Cd * s t - σ * s t'))) ∧
  (∃ c γ₀, 0 < c ∧ 0 < γ₀ ∧ ∀ γ, 0 < γ → γ ≤ γ₀ → ∃ Tγ, ∀ t t', Tγ ≤ t → t ≤ t' →
    ∀ z : ComplexVector n, ‖z‖ ≤ Real.exp (-γ * s t) → ‖F t t' z‖ ≤ Real.exp (-c * γ * s t'))

/-! ## `prop:polynomial-models` (`dynamics.tex:36-72`) and `lem:degree-control` -/

/-- Operator norm of a matrix acting on `ℂⁿ`. -/
def matOpNorm (A : Herm n) : ℝ := ‖Matrix.toEuclideanCLM (n := Fin n) (𝕜 := ℂ) A‖

def PolynomialModels (X : KahlerManifold n) (o : Pt X) (ρ : STF X)
    (F : ℝ → ℝ → ComplexVector n → ComplexVector n) (d : ℕ) (hm Cd Dg : ℝ)
    (tk : ℕ → ℝ) (H Hinv G Ginv : ℕ → PolyMap n) : Prop :=
  let s := fun k => ρ o (tk k)
  let S := fun j : ℕ => Real.exp (hm * j)
  StrictMono tk ∧ Tendsto s atTop atTop ∧
  -- macro grid
  (∃ j₀ : ℕ, ∃ c₁ C₁ : ℝ, 0 < c₁ ∧ s 0 = S j₀ ∧ (∀ j, j₀ ≤ j → ∃ k, s k = S j) ∧
    ∀ j, j₀ ≤ j → (∃ k, s k = S j ∧ s (k + 1) = S (j + 1)) ∨
      (∀ k, S j ≤ s k → s k < S (j + 1) →
        c₁ * Real.sqrt (S j) ≤ s (k + 1) - s k ∧ s (k + 1) - s k ≤ C₁ * Real.sqrt (S j))) ∧
  (∃ ch, 0 < ch ∧ ∃ k₀, ∀ k, k₀ ≤ k →
    ch * Real.sqrt (s k) ≤ s (k + 1) - s k ∧ s (k + 1) - s k ≤ (Real.exp hm - 1) * s k) ∧
  -- normalizations and jet conjugacy `J_d(H_{k+1} ∘ F_k) = J_d(G_k ∘ H_k)`
  (∀ k, (H k).FixesZero ∧ (Hinv k).FixesZero ∧ (Hinv k).degree ≤ d ∧
    (G k).FixesZero ∧ IsPolyAutomorphism (G k) (Ginv k) ∧
    (H k).linearPart.det ≠ 0 ∧ PolyMap.JetEq ((H k).comp (Hinv k)) PolyMap.id d) ∧
  (∀ k, GermJetEq (fun z => (H (k + 1)).eval (F (tk k) (tk (k + 1)) z))
    (fun z => (G k).eval ((H k).eval z)) d) ∧
  (∀ k, ((H k).degree : ℝ) ≤ Dg ∧ ((G k).degree : ℝ) ≤ Dg ∧ ((Ginv k).degree : ℝ) ≤ Dg) ∧
  (∃ η : ℕ → ℝ, Tendsto η atTop (𝓝 0) ∧ ∀ k,
    (H k).coeffNorm ≤ Real.exp (η k * s k) ∧ (Hinv k).coeffNorm ≤ Real.exp (η k * s k) ∧
    (G k).coeffNorm + (Ginv k).coeffNorm ≤ Real.exp (Cd * (s (k + 1) - s k) + η k * s k)) ∧
  (∃ Cp, ∀ k, matOpNorm (H k).linearPart ≤ (1 + s k) ^ Cp ∧
    matOpNorm (H k).linearPart⁻¹ ≤ (1 + s k) ^ Cp ∧
    matOpNorm (G k).linearPart⁻¹ ≤ s k ^ Cp * Real.exp ((s (k + 1) - s k) / 2)) ∧
  -- These are the local polynomial models. Their forward degree is a separate
  -- conclusion (Y04), not an assumption hidden in this predicate.
  (∀ k, IsPolyAutomorphism (forwardComp G k) (backwardComp Ginv k))

/-- Exact forward-degree output of dynamics.tex:70 and 566-575.
Only an unbounded subsequence of macro endpoints is asserted. -/
def ForwardDegreeControl (G : ℕ → PolyMap n) (s : ℕ → ℝ) (hm : ℝ) : Prop :=
  ∃ D : ℝ, 0 < D ∧ ∀ N : ℕ, ∃ j k : ℕ,
    N ≤ j ∧ N ≤ k ∧ s k = Real.exp (hm * j) ∧
      ((forwardComp G k).degree : ℝ) ≤ D * s k

/-! ## `prop:global-coordinates` (`uniformization.tex:172-191`) -/

def GlobalCoordinates (X : KahlerManifold n) (o : Pt X) (ρ : STF X)
    (f : ℝ → Pt X → ComplexVector n) (tk : ℕ → ℝ) (H G Ginv : ℕ → PolyMap n) (σ' γ' : ℝ)
    (Ψ : Pt X → ComplexVector n) (Ψinv : ComplexVector n → Pt X) : Prop :=
  let s := fun k => ρ o (tk k)
  (∀ K : Set (Pt X), IsCompact K →
    TendstoUniformlyOn (fun l x => (backwardComp Ginv l).eval ((H l).eval (f (tk l) x))) Ψ atTop K) ∧
  ContMDiff (ComplexModel n) 𝓘(ℂ, ComplexVector n) ∞ Ψ ∧ Function.Injective Ψ ∧ Ψ o = 0 ∧
  IsOpen (Set.range Ψ) ∧
  ContMDiffOn 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞ Ψinv (Set.range Ψ) ∧
  (∀ x, Ψinv (Ψ x) = x) ∧
  (∀ K ⊆ Set.range Ψ, IsCompact K → ∀ᶠ k in atTop, ∀ z ∈ K,
    ‖(forwardComp G k).eval z‖ ≤ Real.exp (-(σ' / 2) * s k)) ∧
  (∀ᶠ k in atTop, ∀ z : ComplexVector n, ‖z‖ < Real.exp (-γ' * s k) →
    (backwardComp Ginv k).eval z ∈ Set.range Ψ)

/-- The estimates on the exact open coordinate image output by U02.
There is no independent radius predicate or freely assigned differential operator. -/
def ImageDynamics {M : ComplexManifold n}
    (global : Uniformization.OpenCoordinateData n M)
    (G Ginv : ℕ → PolyMap n) (s : ℕ → ℝ) (sigma gamma : ℝ) : Prop :=
  (0 : ComplexVector n) ∈ global.image ∧ Tendsto s atTop atTop ∧
  0 < gamma ∧ gamma < sigma / 2 ∧
  (∀ k, IsPolyAutomorphism (forwardComp G k) (backwardComp Ginv k)) ∧
  (∀ K ⊆ global.image, IsCompact K → ∀ᶠ k in atTop, ∀ z ∈ K,
    ‖(forwardComp G k).eval z‖ ≤ Real.exp (-(sigma / 2) * s k)) ∧
  (∀ᶠ k in atTop, ∀ z : ComplexVector n, ‖z‖ < Real.exp (-gamma * s k) →
    (backwardComp Ginv k).eval z ∈ global.image)

/-- U03 carries the surjectivity proof for this very image into U04. -/
abbrev U03Output {M : ComplexManifold n}
    (global : Uniformization.OpenCoordinateData n M) :=
  Σ' hsurj : global.image = Set.univ, PUnit.{0}

/-- The centered radius in the paper's contradiction. Used only under the
bounded-above/proper-image case, since `sSup` on unbounded real sets is not infinity. -/
def centeredImageRadius (Ω : Set (ComplexVector n)) : ℝ :=
  sSup {R : ℝ | 0 < R ∧ Metric.ball (0 : ComplexVector n) R ⊆ Ω}

/-- The polynomial-growth inequality, uniformization.tex:327-338. -/
def PolynomialGrowthEstimate (n : ℕ) : Prop :=
  ∀ (P : PolyMap n) (m : ℕ), P.degree ≤ m → ∀ R1 R2 : ℝ, 0 < R1 → R1 < R2 →
    ∀ z : ComplexVector n, ‖z‖ < R2 →
      ‖P.eval z‖ ≤ (R2 / R1) ^ m *
        sSup {a : ℝ | ∃ w : ComplexVector n, ‖w‖ < R1 ∧ a = ‖P.eval w‖}

end Yau.Blueprint
