import Yau.Proofs.F01AControlledScalarCaps
import Yau.Proofs.F01ACompactComparisonBounds
import Yau.Proofs.F01PenalizedMajorantWeights
import Yau.Proofs.F01ControlledComparisonQ
import Yau.Proofs.F01LogDetMetricLower
import Yau.Proofs.F01MetricComparisonScalarBounds

/-! One fixed smooth penalized Ricci majorant gives bounds on each
compact core before the approximation level or its solution is chosen.
The upper factor tends to one; the positive lower factor is uniform. -/
noncomputable section
open Set
open scoped ContDiff Matrix ComplexOrder
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint
variable {n : ℕ}

theorem real_metric_upper_order_mono
    {H K : Matrix (Fin n) (Fin n) ℂ} (hH : H.PosSemidef)
    {a b : ℝ} (hab : a ≤ b) (ha : ((a : ℂ) • H - K).PosSemidef) :
    ((b : ℂ) • H - K).PosSemidef := by
  have hd : (((b - a : ℝ) : ℂ) • H).PosSemidef :=
    hH.smul (Complex.zero_le_real.mpr (sub_nonneg.mpr hab))
  have hs := ha.add hd
  convert! hs using 1
  simp only [Complex.ofReal_sub, sub_smul]
  module

theorem actual_compact_uniform_bounds
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u)
    (Ξ : Pt X → ℝ) (hΞ : SmoothFn Ξ)
    (hRic : ∀ x, (levi Ξ x - ricci X.metric.form x).PosSemidef)
    {c : ℝ} (hc : 0 ≤ c)
    (hgrowth : ∀ x, Ξ x ≤ c * (1 + distFrom X.metric.form o x ^ ((3 : ℝ) / 2)))
    {K : Set (Pt X)} (hK : IsCompact K) {T : ℝ} (hT : 0 < T) :
    ∃ a0 L0 A ell R : ℝ,
      0 < a0 ∧ 0 < L0 ∧ 0 ≤ A ∧ 0 < ell ∧ 0 ≤ R ∧
      ∀ (L : ℝ), L0 ≤ L → ∀ ho : u o < L,
        let N := sublevelManifold X.manifold u hu.1 o L ho
        let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
        ∀ (Tsol : ℝ) (h : ℝ → HermitianField N) (U : N.Carrier → ℝ → ℝ),
          T < Tsol → NativePotentialSlab α Tsol h U →
          ∀ x : N.Carrier, x.val ∈ K → ∀ t ∈ Icc 0 T,
            |flowLogDetRatio α h x t| ≤ A ∧ |U x t| ≤ A * t ∧
            flowLogDetTime α h (Icc 0 Tsol) x t ≤ a0 / L ^ 2 ∧
            (gMat (h t) x - (ell : ℂ) • gMat α x).PosSemidef ∧
            ((Real.exp (2 * R / L) : ℂ) • gMat α x - gMat (h t) x).PosSemidef := by
  obtain ⟨a0, ha0, hCaps⟩ := controlled_native_scalar_caps X o u hu
  let D : ℝ := 2 * (T + 1)
  have hD : 0 < D := by dsimp only [D]; positivity
  have hDT : 2 * T ≤ D := by dsimp only [D]; linarith
  obtain ⟨Kex, ε0, Lw, hKex, hε0, hLw, hWeights⟩ :=
    controlled_penalized_majorant_weights X o u hu Ξ hΞ hRic hc hD.le hgrowth
  let ε : ℝ := ε0 / 2
  have hε : 0 < ε := by dsimp only [ε]; positivity
  have hεsmall : ε ≤ ε0 := by dsimp only [ε]; linarith
  let W : Pt X → ℝ := penalizedMajorantWeight Ξ u c Kex ε
  have hW : SmoothFn W := fun a =>
    ((hΞ a).sub (contDiffOn_const.mul ((hu.1 a).pow 2))).sub contDiffOn_const
  obtain ⟨b, hb⟩ := hK.exists_bound_of_continuousOn (continuous_of_smoothFn hW).continuousOn
  let M : ℝ := max 0 b
  have hM : 0 ≤ M := le_max_left _ _
  have hWlo (x : Pt X) (hx : x ∈ K) : -M ≤ W x := by
    have hh : |W x| ≤ b := by simpa only [Real.norm_eq_abs] using hb x hx
    have hMb : b ≤ M := le_max_right _ _
    linarith [neg_abs_le (W x)]
  obtain ⟨Lr, hLr, hRayleigh⟩ := controlled_rayleigh_order X o u hu (by norm_num : (0 : ℝ) < 1 / 2)
  let L0 : ℝ := max 1 (max Lw Lr)
  let R : ℝ := compactComparisonBudget a0 D T M n
  let B : ℝ := compactLogdetLowerBudget a0 D T M n
  let A : ℝ := B + a0 * T
  let ell : ℝ := Real.exp (-(B + (n : ℝ) * (2 * R)))
  have hR : 0 ≤ R := by unfold R compactComparisonBudget; positivity
  have hB : 0 ≤ B := by unfold B compactLogdetLowerBudget; positivity
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  refine ⟨a0, L0, A, ell, R, ha0, ?_, hA, Real.exp_pos _, hR, ?_⟩
  · exact zero_lt_one.trans_le (le_max_left _ _)
  intro L hLL0 ho
  dsimp only
  intro Tsol h U hTsol hslab
  let N := sublevelManifold X.manifold u hu.1 o L ho
  let α := approximatingMetric X.manifold X.metric.form u hu.1 o L ho
  let φ : N.Carrier → ℝ := fun x => W x.val
  let P : N.Carrier → ℝ → ℝ := flowLogDetRatio α h
  let Q : N.Carrier → ℝ → ℝ := comparisonFunction D n U P φ
  have hLone : 1 ≤ L := (le_max_left 1 (max Lw Lr)).trans hLL0
  have hLp : 0 < L := zero_lt_one.trans_le hLone
  have hLw' : Lw ≤ L := (le_max_left Lw Lr).trans ((le_max_right _ _).trans hLL0)
  have hLr' : Lr ≤ L := (le_max_right Lw Lr).trans ((le_max_right _ _).trans hLL0)
  obtain ⟨_, _, hφ, _, hφsign, hφweight⟩ := hWeights ε hε hεsmall L hLw' ho
  obtain ⟨hh0, hh, hU, hU0, Cpre, hCpre, hdata⟩ := hslab
  have hsub : Icc (0 : ℝ) T ⊆ Icc 0 Tsol := fun t ht => ⟨ht.1, ht.2.trans hTsol.le⟩
  have hQ := controlled_short_time_comparison_Q X o u hu ho h U T Cpre D (1 / 2)
    hT hCpre hD.le (by norm_num)
    (fun x i j => (hh x i j).mono (prod_mono Subset.rfl hsub))
    (fun x => (hU x).mono (prod_mono Subset.rfl hsub)) hh0 hU0
    (fun x t ht => (hdata x t (hsub ht)).1)
    (fun x t ht => (hdata x t (hsub ht)).2.1)
    (fun t ht x => (hdata x t (hsub ht)).2.2.1)
    (fun x t ht => ((hdata x t (hsub ht)).2.2.2).mono hsub)
    φ hφ hφsign hφweight
  have hUpper := hRayleigh L hLr' ho h U Tsol T Cpre D hT hTsol hCpre hD.le
    hh hU hh0 hU0 (fun x t ht => (hdata x t ht).1)
    (fun x t ht => (hdata x t ht).2.1)
    (fun t ht x => (hdata x t ht).2.2.1)
    (fun x t ht => (hdata x t ht).2.2.2) φ hφ hφsign hφweight
  have hScalar := hCaps L ho Tsol h U (hT.trans hTsol)
    ⟨hh0, hh, hU, hU0, Cpre, hCpre, hdata⟩
  have hScale : a0 / L ^ 2 ≤ a0 := by
    apply (div_le_iff₀ (sq_pos_of_pos hLp)).mpr
    exact le_mul_of_one_le_right ha0.le (one_le_pow₀ hLone)
  have hRelaxed (x : N.Carrier) (t : ℝ) (ht : t ∈ Icc 0 T) :
      P x t ≤ a0 * t ∧ U x t ≤ a0 * t ^ 2 / 2 := by
    have hh := hScalar x t (hsub ht)
    exact ⟨hh.2.1.trans (mul_le_mul_of_nonneg_right hScale ht.1),
      hh.2.2.trans (div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_right hScale (sq_nonneg t)) (by norm_num))⟩
  have hQB (x : N.Carrier) (hx : x.val ∈ K) (t : ℝ) (ht : t ∈ Icc 0 T) :
      Q x t ≤ R ∧ -B ≤ P x t := by
    exact comparison_scalar_compact_bounds ha0.le hD hT.le hM (Nat.cast_nonneg n)
      hDT ht.1 ht.2 (hRelaxed x t ht).1 (hRelaxed x t ht).2
      (hWlo x.val hx) (hQ.2 x t ht).1
  have hPabs (x : N.Carrier) (hx : x.val ∈ K) (t : ℝ) (ht : t ∈ Icc 0 T) : |P x t| ≤ A := by
    apply abs_le.mpr
    constructor
    · have hh := (hQB x hx t ht).2
      dsimp only [A]
      linarith [mul_nonneg ha0.le hT.le]
    · exact ((hRelaxed x t ht).1.trans (mul_le_mul_of_nonneg_left ht.2 ha0.le)).trans
        (by dsimp only [A]; linarith)
  intro x hx t ht
  have hJ : rayleighPenalty L⁻¹ (Q x t) ≤ 2 * R / L := by
    calc
      _ ≤ 2 * L⁻¹ * Q x t := rayleighPenalty_le_twice_product
        (inv_nonneg.mpr hLp.le) (hQ.2 x t ht).1
      _ ≤ 2 * L⁻¹ * R := mul_le_mul_of_nonneg_left (hQB x hx t ht).1 (by positivity)
      _ = 2 * R / L := by ring
  have hBackground : (gMat α x).PosSemidef :=
    (Yau.LeafProofs.L12Aux.hMat_posDef α x (chartPt x x) (mem_extChartAt_target x)).posSemidef
  have hUpperSmall := real_metric_upper_order_mono hBackground (Real.exp_le_exp.mpr hJ)
    (hUpper x t ht)
  have hExponent : 2 * R / L ≤ 2 * R := div_le_self (by positivity) hLone
  have hUpperFixed := real_metric_upper_order_mono hBackground (Real.exp_le_exp.mpr hExponent)
    hUpperSmall
  refine ⟨hPabs x hx t ht, ?_, (hScalar x t (hsub ht)).1, ?_, hUpperSmall⟩
  · exact closed_potential_abs_bound_of_time_value hT.le (hU0 x)
      (fun t ht => ((hdata x t (hsub ht)).2.2.2).mono hsub)
      (fun t ht => hPabs x hx t ht) t ht
  · exact flow_metric_exp_lower_of_logdet α h (by positivity : 0 ≤ 2 * R) x t
      hUpperFixed (hQB x hx t ht).2

end Yau.NodeProofs.F01Aux
