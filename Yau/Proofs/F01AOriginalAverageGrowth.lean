import Yau.Proofs.F01ASmoothComparison
import Yau.Proofs.P08CanonicalConsequences

/-! The original average-growth constant precedes the actual Riemannian
volume, radius and time. Canonical zeros are removed only on a proved null
set for each such volume. No value assigned to log zero supplies the bound. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal
namespace Yau.NodeProofs.F01Aux
open Yau Yau.Blueprint Yau.Proofs.P04Aux
variable {n : ℕ}

theorem original_average_growth_of_canonical_bound
    (X : KahlerManifold n) (o : Pt X) (u : Pt X → ℝ)
    (hu : ControlledExhaustion X o u) (P ρ : STF X)
    {η : ℝ} (hη : 0 < η) (hcanonical : CanonicalRhoPointBound X o u P η)
    (hsections : CanonicalInitialData X o)
    (hρ : ∀ x t, 0 ≤ t → ρ x t = -P x t) :
    ∀ T, 0 ≤ T → ∃ C : ℝ, ∀ μ, IsRiemannianVolume X.metric.form μ →
      ∀ L, 1 ≤ L → ∀ t ∈ Icc 0 T,
        BallIntegralLE X.metric.form μ o (fun x => ρ x t) L (C * L) := by
  obtain ⟨S, hS, hoS, hgrowth⟩ := hsections.1 o
  obtain ⟨a, ha, hbound⟩ := hcanonical S hS hgrowth
  obtain ⟨C₀, hC₀⟩ := P08Aux.canonical_log_average X o S hS hoS hgrowth
  obtain ⟨K, hK, hcontrolled⟩ := hu.2.2.2
  let Clog : ℝ := max C₀ 0
  have hClog : 0 ≤ Clog := le_max_right _ _
  intro T hT
  let D : ℝ := 2 * (T + 1)
  have hD : 0 < D := by dsimp [D]; linarith
  let κ : ℝ := min (η / (D + 1)) 1
  have hκ : 0 < κ := lt_min (div_pos hη (by linarith)) zero_lt_one
  let B : ℝ := 4 * κ * K ^ 2 + a + a / κ + (n : ℝ)
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨2 * (Clog + B), ?_⟩
  intro μ hμ L hL t ht
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  let ε : ℝ := κ / L
  have hε : 0 < ε := div_pos hκ hLpos
  have hεle : ε ≤ κ := by
    apply (div_le_iff₀ hLpos).mpr
    nlinarith
  have hεadm : ε ≤ η / (D + 1) := hεle.trans (min_le_left _ _)
  have hinv : ε⁻¹ = L / κ := by dsimp [ε]; rw [inv_div]
  have htD : t ∈ Icc 0 (D / 2) := by
    constructor
    · exact ht.1
    · dsimp [D]; linarith [ht.2]
  have hnull := P08Aux.canonical_zero_set_null X o S hS hoS hgrowth μ hμ
  have hnonzero : ∀ᵐ x ∂μ, canonicalNormSq X.metric.form S x ≠ 0 := by
    apply ae_iff.mpr
    simpa only [ne_eq, not_not] using hnull
  have hball : MeasurableSet (distBall X.metric.form o L) :=
    Yau.LeafProofs.L12Aux.measurableSet_distBall X.metric o L
  have hpoint : ∀ᵐ x ∂μ.restrict (distBall X.metric.form o L),
      ρ x t ≤ 2 * (|Real.log (canonicalNormSq X.metric.form S x)| + B * L) := by
    filter_upwards [ae_restrict_of_ae hnonzero, ae_restrict_mem hball] with x hxq hxball
    have hr : distFrom X.metric.form o x < L :=
      (Yau.LeafProofs.L12Aux.mem_distBall_iff X.metric o x hLpos).mp hxball
    have hux : u x ≤ 2 * K * L := by
      have huupper := (hcontrolled x).2.1
      have hkr := mul_le_mul_of_nonneg_left hr.le hK.le
      have hKL := mul_le_mul_of_nonneg_left hL hK.le
      nlinarith
    have hunonneg : 0 ≤ u x := zero_le_one.trans (hu.2.2.1 x)
    have hsquare : u x ^ 2 ≤ (2 * K * L) ^ 2 :=
      (sq_le_sq₀ hunonneg (by positivity)).mpr hux
    have hepssquare : ε * u x ^ 2 ≤ (4 * κ * K ^ 2) * L := by
      calc
        _ ≤ ε * (2 * K * L) ^ 2 := mul_le_mul_of_nonneg_left hsquare hε.le
        _ = _ := by dsimp [ε]; field_simp; ring
    have hqx : 0 < canonicalNormSq X.metric.form S x :=
      lt_of_le_of_ne (canonicalNormSq_nonneg _ _ _) (Ne.symm hxq)
    have hb := hbound D hD ε hε hεadm x t htD hqx
    rw [hinv] at hb
    rw [hρ x t ht.1]
    dsimp [B]
    simp only [div_eq_mul_inv] at hb ⊢
    nlinarith [mul_nonneg (sub_nonneg.mpr hL) ha.le,
      mul_nonneg (sub_nonneg.mpr hL) (Nat.cast_nonneg n)]
  have hlog : (∫⁻ x in distBall X.metric.form o L,
      ENNReal.ofReal |Real.log (canonicalNormSq X.metric.form S x)| ∂μ) ≤
      ENNReal.ofReal (Clog * L) * μ (distBall X.metric.form o L) := by
    exact (hC₀ μ hμ L hL).trans (mul_le_mul'
      (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (le_max_left _ _) hLpos.le)) le_rfl)
  unfold BallIntegralLE
  calc
    _ ≤ ∫⁻ x in distBall X.metric.form o L,
        ENNReal.ofReal (2 * (|Real.log (canonicalNormSq X.metric.form S x)| + B * L)) ∂μ :=
      lintegral_mono_ae (hpoint.mono (fun _ hx => ENNReal.ofReal_le_ofReal hx))
    _ = ENNReal.ofReal 2 * ((∫⁻ x in distBall X.metric.form o L,
        ENNReal.ofReal |Real.log (canonicalNormSq X.metric.form S x)| ∂μ) +
        ENNReal.ofReal (B * L) * μ (distBall X.metric.form o L)) := by
      simp_rw [ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ)),
        ENNReal.ofReal_add (abs_nonneg _) (mul_nonneg hB hLpos.le)]
      rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        lintegral_add_right _ measurable_const]
      simp
    _ ≤ ENNReal.ofReal 2 * (ENNReal.ofReal (Clog * L) * μ (distBall X.metric.form o L) +
        ENNReal.ofReal (B * L) * μ (distBall X.metric.form o L)) := by
      exact mul_le_mul' le_rfl (add_le_add hlog le_rfl)
    _ = ENNReal.ofReal (2 * (Clog + B) * L) * μ (distBall X.metric.form o L) := by
      rw [← add_mul, ← ENNReal.ofReal_add (mul_nonneg hClog hLpos.le)
        (mul_nonneg hB hLpos.le), ← mul_assoc,
        ← ENNReal.ofReal_mul (by norm_num : 0 ≤ (2 : ℝ))]
      congr 2
      ring

end Yau.NodeProofs.F01Aux
