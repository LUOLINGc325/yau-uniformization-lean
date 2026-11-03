import Yau.LeafProofs.L19HeatWeightedEnergyTail
import Yau.LeafProofs.L19HeatC0Initial

/-! Gaussian L² tails for the actual scalar heat family. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology InnerProductSpace ComplexOrder
namespace Yau.LeafProofs.L19Aux
open L18Aux
variable {n : ℕ} {M : ComplexManifold n}
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000

theorem scalarL2Indicator_norm_le {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    ‖scalarL2Indicator μ s hs f‖ ≤ ‖f‖ := by
  apply Lp.norm_le_norm_of_ae_le
  filter_upwards [scalarL2Indicator_coe μ s hs f] with x hx
  rw [hx]
  by_cases hx : x ∈ s <;> simp [hx]

theorem scalarL2Indicator_add {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (f k : Lp ℝ 2 μ) :
    scalarL2Indicator μ s hs (f + k) = scalarL2Indicator μ s hs f + scalarL2Indicator μ s hs k := by
  apply Lp.ext
  filter_upwards [scalarL2Indicator_coe μ s hs (f + k),
    scalarL2Indicator_coe μ s hs f, scalarL2Indicator_coe μ s hs k,
    Lp.coeFn_add f k, Lp.coeFn_add (scalarL2Indicator μ s hs f) (scalarL2Indicator μ s hs k)]
    with x h h₁ h₂ h₃ h₄
  simp only [Pi.add_apply] at h₃ h₄
  rw [h₄, h, h₁, h₂]
  by_cases hx : x ∈ s
  · simpa only [Set.indicator_of_mem hx] using h₃
  · simp only [Set.indicator_of_notMem hx, add_zero]

theorem scalarL2Indicator_add_compl {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (f : Lp ℝ 2 μ) :
    scalarL2Indicator μ s hs f + scalarL2Indicator μ sᶜ hs.compl f = f := by
  apply Lp.ext
  filter_upwards [scalarL2Indicator_coe μ s hs f,
    scalarL2Indicator_coe μ sᶜ hs.compl f,
    Lp.coeFn_add (scalarL2Indicator μ s hs f) (scalarL2Indicator μ sᶜ hs.compl f)]
    with x h₁ h₂ h₃
  simp only [Pi.add_apply] at h₃
  rw [h₃, h₁, h₂]
  by_cases hx : x ∈ s <;> simp [hx]

theorem scalarL2Indicator_inner_of_support {X : Type*} [MeasurableSpace X] (μ : Measure X)
    (s : Set X) (hs : MeasurableSet s) (f k : Lp ℝ 2 μ)
    (hk : ∀ᵐ x ∂μ, x ∉ s → k x = 0) :
    ⟪k, f⟫_ℝ = ⟪k, scalarL2Indicator μ s hs f⟫_ℝ := by
  rw [L2.inner_def, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [scalarL2Indicator_coe μ s hs f, hk] with x hx hkx
  rw [hx]
  by_cases hxs : x ∈ s
  · rw [Set.indicator_of_mem hxs]
  · simp [hkx hxs]

theorem scalarGaussianL2_coe (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) (a : ℝ) (ha : 0 < a) :
    scalarGaussianL2 g hK hRic μ hμ o a ha =ᵐ[μ]
      (fun x => Real.exp (-a * inducedDistance g.form o x ^ 2)) := by
  filter_upwards [(gaussianWeight_memLp_two g hK hRic μ hμ o ha).coeFn_toLp] with x hx
  change scalarGaussianL2 g hK hRic μ hμ o a ha x = _
  simpa only [scalarGaussianL2, gaussianWeight, neg_mul] using hx

/-- The initial Gaussian tail is dominated by a wider Gaussian with an
exponentially small scalar coefficient. -/
theorem scalarGaussianL2_initial_tail (g : SmoothMetric M) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef) (μ : Measure M.Carrier)
    (hμ : IsRiemannianVolume g.form μ) (o : M.Carrier) (a : ℝ) (ha : 0 < a)
    (R : ℝ) (hR : 0 < R) :
    ‖scalarL2Indicator μ (distBall g.form o (R / 2))ᶜ
      (L12Aux.measurableSet_distBall g o (R / 2)).compl
      (scalarGaussianL2 g hK hRic μ hμ o a ha)‖ ≤
      Real.exp (-a * R ^ 2 / 8) *
        ‖scalarGaussianL2 g hK hRic μ hμ o (a / 2) (by positivity)‖ := by
  apply Lp.norm_le_mul_norm_of_ae_le_mul
  filter_upwards [scalarL2Indicator_coe μ (distBall g.form o (R / 2))ᶜ
      (L12Aux.measurableSet_distBall g o (R / 2)).compl
      (scalarGaussianL2 g hK hRic μ hμ o a ha),
    scalarGaussianL2_coe g hK hRic μ hμ o a ha,
    scalarGaussianL2_coe g hK hRic μ hμ o (a / 2) (by positivity)] with x hi hf hk
  rw [hi, hk]
  by_cases hx : x ∈ (distBall g.form o (R / 2))ᶜ
  · rw [Set.indicator_of_mem hx, hf]
    simp only [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hd : R / 2 ≤ inducedDistance g.form o x := by
      exact le_of_not_gt (fun hh => hx ((L12Aux.mem_distBall_iff g o x (by positivity)).mpr hh))
    have hd0 := g.induced_distance_nonneg o x
    have hsq : R ^ 2 / 4 ≤ inducedDistance g.form o x ^ 2 := by nlinarith
    nlinarith [mul_nonneg ha.le (sub_nonneg.mpr hsq)]
  · rw [Set.indicator_of_notMem hx, norm_zero]
    positivity

/-- Splitting the initial datum at half the observation radius reduces
heat tails to one actual Davies--Gaffney estimate and one contraction. -/
theorem scalarHeatFamily_split_tail (g : SmoothMetric M)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (R t A : ℝ) (hR : 0 < R) (f : Lp ℝ 2 μ)
    (hDG : ∀ k : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, x ∉ distBall g.form o (R / 2) → k x = 0) →
      ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t k)‖ ≤
        Real.exp (-R ^ 2 / (8 * A ^ 2 * t)) * ‖k‖) :
    ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
      (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t f)‖ ≤
      Real.exp (-R ^ 2 / (8 * A ^ 2 * t)) * ‖f‖ +
      ‖scalarL2Indicator μ (distBall g.form o (R / 2))ᶜ
        (L12Aux.measurableSet_distBall g o (R / 2)).compl f‖ := by
  let S := distBall g.form o (R / 2)
  have hS := L12Aux.measurableSet_distBall g o (R / 2)
  let fi := scalarL2Indicator μ S hS f
  let fo := scalarL2Indicator μ Sᶜ hS.compl f
  have hfi : ∀ᵐ x ∂μ, x ∉ S → fi x = 0 := by
    filter_upwards [scalarL2Indicator_coe μ S hS f] with x hx hxs
    exact hx.trans (Set.indicator_of_notMem hxs _)
  have hsplit : f = fi + fo := (scalarL2Indicator_add_compl μ S hS f).symm
  calc
    _ = ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t fi) +
      scalarL2Indicator μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t fo)‖ := by
      conv_lhs => rw [hsplit, map_add, scalarL2Indicator_add]
    _ ≤ ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t fi)‖ +
      ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t fo)‖ := norm_add_le _ _
    _ ≤ Real.exp (-R ^ 2 / (8 * A ^ 2 * t)) * ‖fi‖ + ‖fo‖ :=
      add_le_add (hDG fi hfi) ((scalarL2Indicator_norm_le _ _ _ _).trans
        (scalarHeatFamily_norm_le g μ hμ t fo))
    _ ≤ _ := add_le_add (mul_le_mul_of_nonneg_left
      (scalarL2Indicator_norm_le μ S hS f) (Real.exp_pos _).le) le_rfl

/-- The actual flow of a Gaussian has uniform Gaussian L² tails on every
positive time slab. The dimensional constant is chosen before the geometry;
the other constants may depend on the initial Gaussian and the slab. -/
theorem exists_uniform_gaussian_heat_L2_tail (n : ℕ) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ (M : ComplexManifold n) (g : SmoothMetric M)
      (hK : IsKahler g) (hRic : ∀ x, (ricci g.form x).PosSemidef)
      (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
      (o : M.Carrier) (a b : ℝ) (ha : 0 < a), 0 < b →
      ∃ C β : ℝ, 0 < C ∧ 0 < β ∧ ∀ (R t : ℝ), 0 < R → 0 < t → t ≤ b →
        ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
          (L12Aux.measurableSet_distBall g o R).compl
          (scalarHeatFamily g μ hμ t (scalarGaussianL2 g hK hRic μ hμ o a ha))‖ ≤
          C * Real.exp (-β * R ^ 2) := by
  obtain ⟨A, hA, hDG⟩ := exists_uniform_annular_heat_L2_tail n
  refine ⟨A, hA, ?_⟩
  intro M g hK hRic μ hμ o a b ha hb
  let f := scalarGaussianL2 g hK hRic μ hμ o a ha
  let k := scalarGaussianL2 g hK hRic μ hμ o (a / 2) (by positivity)
  let β := min (1 / (8 * A ^ 2 * b)) (a / 8)
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  have hβ : 0 < β := lt_min (by positivity) (by positivity)
  refine ⟨‖f‖ + ‖k‖ + 1, β, by positivity, hβ, ?_⟩
  intro R t hR ht htb
  have hdg : ∀ q : Lp ℝ 2 μ,
      (∀ᵐ x ∂μ, x ∉ distBall g.form o (R / 2) → q x = 0) →
      ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t q)‖ ≤
        Real.exp (-R ^ 2 / (8 * A ^ 2 * t)) * ‖q‖ := by
    intro q hq
    have hd := hDG M g μ hμ o (R / 2) R (by positivity) (by linarith) t ht q hq
    convert hd using 2 <;> congr 1 <;> ring
  have hsplit := scalarHeatFamily_split_tail g μ hμ o R t A hR f hdg
  have hinit := scalarGaussianL2_initial_tail g hK hRic μ hμ o a ha R hR
  have he₁ : Real.exp (-R ^ 2 / (8 * A ^ 2 * t)) ≤ Real.exp (-β * R ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hβ₁ := min_le_left (1 / (8 * A ^ 2 * b)) (a / 8)
    have hd₁ : 0 < 8 * A ^ 2 * t := by positivity
    have hd₂ : 0 < 8 * A ^ 2 * b := by positivity
    have hrec : 1 / (8 * A ^ 2 * b) ≤ 1 / (8 * A ^ 2 * t) :=
      one_div_le_one_div_of_le hd₁ (by nlinarith [sq_nonneg A])
    have hh : β ≤ 1 / (8 * A ^ 2 * t) := hβ₁.trans hrec
    calc
      _ = -(1 / (8 * A ^ 2 * t)) * R ^ 2 := by ring
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg R)]
  have he₂ : Real.exp (-a * R ^ 2 / 8) ≤ Real.exp (-β * R ^ 2) := by
    apply Real.exp_le_exp.mpr
    have hh : β ≤ a / 8 := min_le_right _ _
    nlinarith [mul_nonneg (sub_nonneg.mpr hh) (sq_nonneg R)]
  calc
    _ ≤ Real.exp (-R ^ 2 / (8 * A ^ 2 * t)) * ‖f‖ +
        Real.exp (-a * R ^ 2 / 8) * ‖k‖ := hsplit.trans (add_le_add le_rfl hinit)
    _ ≤ Real.exp (-β * R ^ 2) * ‖f‖ + Real.exp (-β * R ^ 2) * ‖k‖ :=
      add_le_add (mul_le_mul_of_nonneg_right he₁ (norm_nonneg _))
        (mul_le_mul_of_nonneg_right he₂ (norm_nonneg _))
    _ ≤ _ := by nlinarith [Real.exp_pos (-β * R ^ 2)]

/-- Inputs supported in a fixed ball have uniform Gaussian L² tails for
all positive times bounded above. No regularity of the initial input is needed. -/
theorem scalarHeatFamily_compact_support_gaussian_L2_tail
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (o : M.Carrier) (r b : ℝ) (hr : 0 < r) (hb : 0 < b) (f : Lp ℝ 2 μ)
    (hf : ∀ᵐ x ∂μ, x ∉ distBall g.form o r → f x = 0) :
    ∃ C β : ℝ, 0 < C ∧ 0 < β ∧ ∀ (R t : ℝ), 0 < R → 0 < t → t ≤ b →
      ‖scalarL2Indicator μ (distBall g.form o R)ᶜ
        (L12Aux.measurableSet_distBall g o R).compl (scalarHeatFamily g μ hμ t f)‖ ≤
        C * Real.exp (-β * R ^ 2) := by
  obtain ⟨A, hA, hDG⟩ := exists_uniform_annular_heat_L2_tail n
  have hApos : 0 < A := lt_of_lt_of_le zero_lt_one hA
  let β := 1 / (8 * A ^ 2 * b)
  have hβ : 0 < β := by dsimp only [β]; positivity
  let K := Real.exp (4 * β * r ^ 2)
  have hK : 1 ≤ K := Real.one_le_exp_iff.mpr (by dsimp only [β]; positivity)
  refine ⟨K * (‖f‖ + 1), β, by dsimp only [K]; positivity, hβ, ?_⟩
  intro R t hR ht htb
  by_cases hlarge : 2 * r < R
  · have hgap : r < R := by linarith
    have hd := hDG M g μ hμ o r R hr hgap t ht f hf
    have he : Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) ≤ Real.exp (-β * R ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hden : 0 < 2 * A ^ 2 * t := by positivity
      rw [div_le_iff₀ hden]
      have hsq : R ^ 2 / 4 ≤ (R - r) ^ 2 := by nlinarith
      have hβt : β * (2 * A ^ 2 * t) ≤ 1 / 4 := by
        dsimp only [β]
        rw [div_mul_eq_mul_div, one_mul]
        apply (div_le_iff₀ (by positivity : 0 < 8 * A ^ 2 * b)).mpr
        nlinarith [mul_nonneg (sq_nonneg A) (sub_nonneg.mpr htb)]
      have hh := mul_le_mul_of_nonneg_right hβt (sq_nonneg R)
      nlinarith
    calc
      _ ≤ Real.exp (-(R - r) ^ 2 / (2 * A ^ 2 * t)) * ‖f‖ := hd
      _ ≤ Real.exp (-β * R ^ 2) * ‖f‖ := mul_le_mul_of_nonneg_right he (norm_nonneg _)
      _ ≤ _ := by nlinarith [Real.exp_pos (-β * R ^ 2), mul_nonneg (sub_nonneg.mpr hK) (norm_nonneg f)]
  · have hexp : 1 ≤ K * Real.exp (-β * R ^ 2) := by
      rw [← Real.exp_add]
      apply Real.one_le_exp_iff.mpr
      have hsq : R ^ 2 ≤ 4 * r ^ 2 := by nlinarith
      nlinarith [mul_nonneg hβ.le (sub_nonneg.mpr hsq)]
    calc
      _ ≤ ‖f‖ := (scalarL2Indicator_norm_le _ _ _ _).trans (scalarHeatFamily_norm_le g μ hμ t f)
      _ ≤ _ := by nlinarith [mul_nonneg (sub_nonneg.mpr hexp) (norm_nonneg f), Real.exp_pos (-β * R ^ 2)]

end Yau.LeafProofs.L19Aux
