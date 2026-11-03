import Yau.Proofs.F01ASmoothComparison
import Yau.Proofs.F01AInterfaces
import Yau.Proofs.F01ControlledComparisonQ
import Yau.Proofs.F01ApproximatingSquareLevi
import Yau.Proofs.F01CompactApproximationIdentity

/-! Every smooth Ricci-weight comparison passes through the same actual
approximating family and the same already chosen subsequence. The uniform
epsilon coefficient is chosen before the horizon and the smooth weight. -/
noncomputable section
open Set Filter
open scoped Topology ContDiff Matrix ComplexOrder

namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}
set_option backward.isDefEq.respectTransparency false

/-- The exhaustion fixes one admissibility coefficient for every horizon and
every smooth Ricci majorant. Only the approximation-level threshold depends
on the horizon. -/
theorem controlled_uniform_comparison_weights
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) :
    ∃ η : ℝ, 0 < η ∧ ∀ D : ℝ, 0 < D → ∃ L0 : ℝ, 0 < L0 ∧
      ∀ (ψ : Pt X → ℝ), SmoothFn ψ →
        (∀ x, HermLE (ricci X.metric.form x) (levi ψ x)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ η / (D + 1) →
      ∀ A L : ℝ, L0 ≤ L → ∀ ho : u o < L,
      ∀ x : (sublevelManifold X.manifold u hu.1 o L ho).Carrier,
        (gMat (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x -
          (D : ℂ) • ricci (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x +
          (D : ℂ) • levi (fun y : (sublevelManifold X.manifold u hu.1 o L ho).Carrier =>
            ψ y.val - ε * u y.val ^ 2 - A) x -
          ((1 / 2 : ℝ) : ℂ) •
            gMat (approximatingMetric X.manifold X.metric.form u hu.1 o L ho) x).PosSemidef := by
  obtain ⟨K, hK, hsquare⟩ := controlled_approximating_square_levi X o u hu
  obtain ⟨G, hG, B, hB, hbudgets⟩ := controlled_conformal_gradient_levi X o u hu
  let η := 1 / (4 * (K + 1))
  have hη : 0 < η := by dsimp only [η]; positivity
  refine ⟨η, hη, ?_⟩
  intro D hD
  let L0 := 4 * D * (n : ℝ) * B + 1
  have hL0 : 0 < L0 := by dsimp only [L0]; positivity
  refine ⟨L0, hL0, ?_⟩
  intro ψ hψ hRic ε hε hεsmall A L hLL0 ho x
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hL1 : 1 ≤ L := by
    have hk : 0 ≤ 4 * D * (n : ℝ) * B := by positivity
    dsimp only [L0] at hLL0
    linarith
  have hL : 0 < L := zero_lt_one.trans_le hL1
  have herr : D * (n : ℝ) * (B / L ^ 2) ≤ 1 / 4 := by
    have hlarge : 4 * D * (n : ℝ) * B ≤ L ^ 2 := by
      dsimp only [L0] at hLL0
      nlinarith
    have he : D * (n : ℝ) * (B / L ^ 2) = D * (n : ℝ) * B / L ^ 2 := by ring
    rw [he]
    apply (div_le_iff₀ (sq_pos_of_pos hL)).mpr
    nlinarith
  have hpenalty : D * ε * K ≤ 1 / 4 := by
    have hsmall : ε ≤ 1 / (4 * (D + 1) * (K + 1)) := by
      calc
        ε ≤ η / (D + 1) := hεsmall
        _ = 1 / (4 * (D + 1) * (K + 1)) := by
          dsimp only [η]
          rw [div_div]
          congr 1
          ring
    have hden : 0 < 4 * (D + 1) * (K + 1) := by positivity
    have hh := (le_div_iff₀ hden).mp hsmall
    have hcoef : 4 * D * K ≤ 4 * (D + 1) * (K + 1) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hcoef hε.le
    nlinarith
  have hψr : SmoothFn (M := N) (fun y => ψ y.val) :=
    smoothFn_openRestriction X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) hψ
  have hur : SmoothFn (M := N) (fun y => u y.val) :=
    smoothFn_openRestriction X.manifold (sublevelOpens X.manifold u hu.1 o L)
      (sublevelComponent_isConnected ho) hu.1
  have hu2 : SmoothFn (M := N) (fun y => u y.val ^ 2) := fun a => (hur a).pow 2
  have hεu2 : SmoothFn (M := N) (fun y => ε * u y.val ^ 2) :=
    fun a => contDiffOn_const.mul (hu2 a)
  have hdiff : SmoothFn (M := N) (fun y => ψ y.val - ε * u y.val ^ 2) :=
    fun a => (hψr a).sub (hεu2 a)
  have hA : SmoothFn (M := N) (fun _ => A) := fun _ => contDiffOn_const
  have hlevi : levi (fun y : N.Carrier => ψ y.val - ε * u y.val ^ 2 - A) x =
      levi ψ x.val - (ε : ℂ) • levi (fun y : N.Carrier => u y.val ^ 2) x := by
    rw [levi_sub_native hdiff hA, levi_const_native, sub_zero,
      levi_sub_native hψr hεu2, levi_const_mul_native hu2 ε]
    exact congrArg
      (fun Z : Matrix (Fin n) (Fin n) ℂ => Z -
        (ε : ℂ) • levi (fun y : N.Carrier => u y.val ^ 2) x)
      (openRestriction_levi X.manifold (sublevelOpens X.manifold u hu.1 o L)
        (sublevelComponent_isConnected ho) ψ x)
  have hαpos : (gMat α x).PosDef :=
    LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)
  have hremaining : 0 ≤ 1 - 1 / 2 - D * (n : ℝ) * (B / L ^ 2) - D * ε * K := by
    linarith
  have p1 := hαpos.posSemidef.smul (Complex.zero_le_real.mpr hremaining)
  have p2 := ((hbudgets L ho x).2.1).smul
    (Complex.zero_le_real.mpr (mul_nonneg hD.le hn))
  have p3 := (show (levi ψ x.val - ricci X.metric.form x.val).PosSemidef from hRic x.val).smul
    (Complex.zero_le_real.mpr hD.le)
  have p4 := (hsquare L ho x).smul (Complex.zero_le_real.mpr (mul_nonneg hD.le hε.le))
  rw [approximatingMetric_ricci X.metric.form
    (LeafProofs.L12Aux.metricSmooth_of_smoothMetric X.metric) u hu.1 o hL ho x, hlevi]
  convert p3.add (p2.add (p4.add p1)) using 1
  ext i j
  simp only [Matrix.sub_apply, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  dsimp only [gMat, α]
  push_cast
  ring

/-- A finite comparison holds eventually at every queried ambient point, for
the actual continued solution already chosen at each level. The extension
identities merely identify its two scalar values on that open manifold. -/
theorem actual_approximation_eventual_smooth_comparison
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (L : ℕ → ℝ) (ho : ∀ m, u o < L m)
    (h : ∀ m, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (V : ∀ m, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (V m))
    (Us Ps : ℕ → STF X)
    (hUs : ∀ (m : ℕ)
      (x : (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier) (t : ℝ),
      Us m x.val t = V m x t)
    (hPs : ∀ (m : ℕ)
      (x : (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier) (t : ℝ),
      Ps m x.val t = flowLogDetRatio
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)) (h m) x t) :
    ∃ η : ℝ, 0 < η ∧ ∀ D : ℝ, 0 < D →
      ∀ ψ : Pt X → ℝ, SmoothFn ψ →
        (∀ x, HermLE (ricci X.metric.form x) (levi ψ x)) →
      ∀ ε : ℝ, 0 < ε → ε ≤ η / (D + 1) →
      ∀ A : ℝ, (∀ x, ψ x - ε * u x ^ 2 - A ≤ 0) →
      ∀ x t, t ∈ Icc 0 (D / 2) → ∀ᶠ m in atTop,
        0 ≤ (D - t) * Ps m x t + Us m x t -
          D * (ψ x - ε * u x ^ 2 - A) + (n : ℝ) * t := by
  obtain ⟨η, hη, hweights⟩ := controlled_uniform_comparison_weights X o u hu
  refine ⟨η, hη, ?_⟩
  intro D hD ψ hψ hRic ε hε hεsmall A hsign x t ht
  obtain ⟨L0, _, hweight⟩ := hweights D hD
  obtain ⟨Lc, _, hcore⟩ := compact_approximation_identity X o u hu
    (isCompact_singleton : IsCompact ({x} : Set (Pt X)))
  obtain ⟨N, hN⟩ := exists_nat_gt (D / 2)
  filter_upwards [hL.eventually (eventually_ge_atTop L0),
    hL.eventually (eventually_ge_atTop Lc), eventually_ge_atTop N] with m hm hmcore hmN
  let Nm := sublevelManifold X.manifold u hu.1 o (L m) (ho m)
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)
  let xm : Nm.Carrier := ⟨x, (hcore (L m) hmcore (ho m)).1 (mem_singleton x)⟩
  have hT : 0 < (m : ℝ) + 2 := by positivity
  have htime : D / 2 ≤ (m : ℝ) + 2 := by
    have hcast : (N : ℝ) ≤ m := by exact_mod_cast hmN
    linarith
  have htm : t ∈ Icc 0 ((m : ℝ) + 2) := ⟨ht.1, ht.2.trans htime⟩
  obtain ⟨hh0, hh, hV, hV0, C, hC, hdata⟩ := hsol m
  let φ : Nm.Carrier → ℝ := fun y => ψ y.val - ε * u y.val ^ 2 - A
  have hφ : SmoothFn φ := by
    have hψr := smoothFn_openRestriction X.manifold
      (sublevelOpens X.manifold u hu.1 o (L m)) (sublevelComponent_isConnected (ho m)) hψ
    have hur := smoothFn_openRestriction X.manifold
      (sublevelOpens X.manifold u hu.1 o (L m)) (sublevelComponent_isConnected (ho m)) hu.1
    exact fun a => ((hψr a).sub (contDiffOn_const.mul ((hur a).pow 2))).sub contDiffOn_const
  have hQ := controlled_short_time_comparison_Q X o u hu (ho m) (h m) (V m)
    ((m : ℝ) + 2) C D (1 / 2) hT hC hD.le (by norm_num) hh hV hh0 hV0
    (fun y s hs => (hdata y s hs).1) (fun y s hs => (hdata y s hs).2.1)
    (fun s hs y => (hdata y s hs).2.2.1) (fun y s hs => (hdata y s hs).2.2.2)
    φ hφ (fun y => hsign y.val) (hweight ψ hψ hRic ε hε hεsmall A (L m) hm (ho m))
  have hQx := (hQ.2 xm t htm).1
  change 0 ≤ (D - t) * flowLogDetRatio α (h m) xm t + V m xm t -
    D * (ψ xm.val - ε * u xm.val ^ 2 - A) + (n : ℝ) * t at hQx
  rw [← hPs m xm t, ← hUs m xm t] at hQx
  exact hQx

/-- The actual same-family comparison. The common potential, scalar field
and subsequence are supplied once, before any horizon or weight is queried;
only their genuine point-value limits are consumed by this thin bridge. -/
theorem actual_smooth_comparison_of_same_sequence
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (L : ℕ → ℝ) (ho : ∀ m, u o < L m)
    (h : ∀ m, ℝ → HermitianField (sublevelManifold X.manifold u hu.1 o (L m) (ho m)))
    (V : ∀ m, (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier → ℝ → ℝ)
    (hL : Tendsto L atTop atTop)
    (hsol : ∀ m, NativePotentialSlab
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m))
      ((m : ℝ) + 2) (h m) (V m))
    (Us Ps : ℕ → STF X)
    (hUs : ∀ (m : ℕ)
      (x : (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier) (t : ℝ),
      Us m x.val t = V m x t)
    (hPs : ∀ (m : ℕ)
      (x : (sublevelManifold X.manifold u hu.1 o (L m) (ho m)).Carrier) (t : ℝ),
      Ps m x.val t = flowLogDetRatio
      (approximatingMetric X.manifold X.metric.form u hu.1 o (L m) (ho m)) (h m) x t)
    (U P : STF X) (σ : ℕ → ℕ) (hσ : StrictMono σ)
    (hU : ∀ x t, 0 ≤ t → Tendsto (fun m => Us (σ m) x t) atTop (𝓝 (U x t)))
    (hP : ∀ x t, 0 ≤ t → Tendsto (fun m => Ps (σ m) x t) atTop (𝓝 (P x t))) :
    ∃ η : ℝ, 0 < η ∧ SmoothRicciWeightComparison X u U P η := by
  obtain ⟨η, hη, hfinite⟩ := actual_approximation_eventual_smooth_comparison
    X o u hu L ho h V hL hsol Us Ps hUs hPs
  refine ⟨η, hη, ?_⟩
  intro D hD ψ hψ hRic ε hε hεsmall A hsign x t ht
  have hlim : Tendsto (fun m => (D - t) * Ps (σ m) x t + Us (σ m) x t -
      D * (ψ x - ε * u x ^ 2 - A) + (n : ℝ) * t) atTop
      (𝓝 ((D - t) * P x t + U x t -
        D * (ψ x - ε * u x ^ 2 - A) + (n : ℝ) * t)) :=
    (((tendsto_const_nhds.mul (hP x t ht.1)).add (hU x t ht.1)).sub
      tendsto_const_nhds).add tendsto_const_nhds
  exact ge_of_tendsto hlim
    (hσ.tendsto_atTop.eventually (hfinite D hD ψ hψ hRic ε hε hεsmall A hsign x t ht))

end Yau.NodeProofs.F01Aux
