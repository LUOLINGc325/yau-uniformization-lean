import Yau.LeafProofs.L18
import Yau.LeafProofs.L12Complete

/-! The quantitative L² mean-value estimate implies the frozen p=1 L18
statement for the original balls and their actual Riemannian volume. -/

open MeasureTheory Filter
open scoped Topology ContDiff Manifold ENNReal Matrix ComplexOrder

noncomputable section

namespace Yau.LeafProofs.L18Aux

/-- The concrete intermediate estimate in the Moser argument. All geometric,
smoothness and measure data are precisely the original leaf data. -/
def BallL2MeanValueEstimate (n : ℕ) (A : ℝ) (N : ℕ) : Prop :=
  ∀ (M : ComplexManifold n) (g : SmoothMetric M),
    IsComplete g → IsKahler g →
    (∀ x, (ricci g.form x).PosSemidef) →
    ∀ μ, IsRiemannianVolume g.form μ →
    ∀ u : M.Carrier → ℝ, SmoothFn u →
      (∀ x, 0 ≤ u x) → (∀ x, 0 ≤ laplacian g.form u x) →
      ∀ x r R, 0 < r → r < R →
        (sSup (u '' distBall g.form x r)) ^ 2 ≤
          A * (R / (R - r)) ^ N / μ.real (distBall g.form x R) *
            ∫ y in distBall g.form x R, u y ^ 2 ∂μ

private def interpolationRadius (r : ℝ) (i : ℕ) : ℝ :=
  r * (1 - (1 / 2 : ℝ) ^ (i + 1))

private theorem interpolationRadius_bounds {r : ℝ} (hr : 0 < r) (i : ℕ) :
    0 < interpolationRadius r i ∧
      interpolationRadius r i < r ∧ r / 2 ≤ interpolationRadius r i := by
  have hp : 0 < (1 / 2 : ℝ) ^ (i + 1) := by positivity
  have hle : (1 / 2 : ℝ) ^ (i + 1) ≤ 1 / 2 := by
    simpa only [pow_one] using
      pow_le_pow_of_le_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
        (by norm_num : (1 / 2 : ℝ) ≤ 1) (by omega : 1 ≤ i + 1)
  dsimp [interpolationRadius]
  constructor
  · exact mul_pos hr (by linarith)
  constructor
  · nlinarith
  · nlinarith

private theorem interpolationRadius_succ {r : ℝ} (hr : 0 < r) (i : ℕ) :
    interpolationRadius r i < interpolationRadius r (i + 1) ∧
      interpolationRadius r (i + 1) /
          (interpolationRadius r (i + 1) - interpolationRadius r i) ≤
        (2 : ℝ) ^ (i + 2) := by
  have hp : 0 < (1 / 2 : ℝ) ^ (i + 1) := by positivity
  have hdiff : interpolationRadius r (i + 1) - interpolationRadius r i =
      r * (1 / 2 : ℝ) ^ (i + 2) := by
    simp only [interpolationRadius, pow_succ]
    ring
  have hdiffpos : 0 < interpolationRadius r (i + 1) - interpolationRadius r i := by
    rw [hdiff]
    positivity
  refine ⟨sub_pos.mp hdiffpos, ?_⟩
  apply (div_le_iff₀ hdiffpos).mpr
  rw [hdiff]
  have heq : (2 : ℝ) ^ (i + 2) * (1 / 2 : ℝ) ^ (i + 2) = 1 := by
    rw [← mul_pow]
    norm_num
  have hprod : (2 : ℝ) ^ (i + 2) * (r * (1 / 2 : ℝ) ^ (i + 2)) = r := by
    calc
      _ = r * ((2 : ℝ) ^ (i + 2) * (1 / 2 : ℝ) ^ (i + 2)) := by ring
      _ = r := by rw [heq, mul_one]
  rw [hprod]
  exact (interpolationRadius_bounds hr (i + 1)).2.1.le

private theorem distBall_volume_lt_top {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) :
    μ (distBall g.form x r) < ⊤ := by
  let : IsLocallyFiniteMeasure μ := riemannianVolume_locallyFinite g μ hμ
  apply lt_of_le_of_lt (measure_mono ?_)
    (L12Aux.isCompact_inducedDistance_sublevel g x r).measure_lt_top
  intro y hy
  exact ((L12Aux.mem_distBall_iff g x y hr).mp hy).le

/-- The actual Bishop--Gromov theorem gives a uniform volume denominator
throughout the concentric interpolation sequence. -/
private theorem interpolation_volume_bound {n : ℕ} {M : ComplexManifold n}
    (g : SmoothMetric M) (hcomplete : IsComplete g) (hK : IsKahler g)
    (hRic : ∀ x, (ricci g.form x).PosSemidef)
    (μ : Measure M.Carrier) (hμ : IsRiemannianVolume g.form μ)
    (x : M.Carrier) {r : ℝ} (hr : 0 < r) (i : ℕ) :
    μ.real (distBall g.form x r) ≤
      (2 : ℝ) ^ (2 * n) * μ.real (distBall g.form x (interpolationRadius r i)) := by
  have hρ := interpolationRadius_bounds hr i
  have hbg := Yau.LeafProofs.L12 n M g hcomplete hK hRic μ hμ x
    (interpolationRadius r i) r hρ.1 hρ.2.1.le
  have hratio : r / interpolationRadius r i ≤ 2 := by
    apply (div_le_iff₀ hρ.1).mpr
    linarith [hρ.2.2]
  have hpow : (r / interpolationRadius r i) ^ (2 * n) ≤ (2 : ℝ) ^ (2 * n) :=
    pow_le_pow_left₀ (div_nonneg hr.le hρ.1.le) hratio _
  have hbg' : μ (distBall g.form x r) ≤
      ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) *
        μ (distBall g.form x (interpolationRadius r i)) :=
    hbg.trans (by gcongr)
  have ht : ENNReal.ofReal ((2 : ℝ) ^ (2 * n)) *
      μ (distBall g.form x (interpolationRadius r i)) ≠ ⊤ :=
    (ENNReal.mul_lt_top ENNReal.ofReal_lt_top
      (distBall_volume_lt_top g μ hμ x hρ.1)).ne
  have hreal := ENNReal.toReal_mono ht hbg'
  simpa only [ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity :
    (0 : ℝ) ≤ 2 ^ (2 * n)), Measure.real_def] using hreal

/-- Closing the explicit L² intermediate estimate proves the original L18
with no extra assumption on its geometric data or volume measure. -/
theorem liSchoenMeanValue_of_ballL2Estimate
    (h : ∀ n > 0, ∃ A : ℝ, 0 < A ∧ ∃ N : ℕ, BallL2MeanValueEstimate n A N) :
    Yau.LeafObligations.L18 := by
  intro n hn
  obtain ⟨A, hA, N, hL2⟩ := h n hn
  let D : ℝ := (2 : ℝ) ^ (2 * n)
  let E : ℝ := A * (2 : ℝ) ^ (2 * N) * D
  let b : ℝ := (2 : ℝ) ^ N
  refine ⟨b * E, by dsimp [b, E, D]; positivity, ?_⟩
  intro M g hcomplete hK hRic μ hμ u hu hnonneg x r hr
  have hu0 : ∀ y, 0 ≤ u y := fun y => (hnonneg y).1
  have husub : ∀ y, 0 ≤ laplacian g.form u y := fun y => (hnonneg y).2
  let ρ : ℕ → ℝ := interpolationRadius r
  let S : ℕ → Set M.Carrier := fun i => distBall g.form x (ρ i)
  let T : Set M.Carrier := distBall g.form x r
  let V : ℝ := μ.real T
  have hρ (i : ℕ) : 0 < ρ i ∧ ρ i < r ∧ r / 2 ≤ ρ i :=
    interpolationRadius_bounds hr i
  have hρstep (i : ℕ) : ρ i < ρ (i + 1) ∧
      ρ (i + 1) / (ρ (i + 1) - ρ i) ≤ (2 : ℝ) ^ (i + 2) :=
    interpolationRadius_succ hr i
  have hS (i : ℕ) : MeasurableSet (S i) :=
    (L12Aux.isOpen_distBall g x (ρ i)).measurableSet
  have hST (i : ℕ) : S i ⊆ T := by
    intro y hy
    exact (L12Aux.mem_distBall_iff g x y hr).mpr
      (((L12Aux.mem_distBall_iff g x y (hρ i).1).mp hy).trans (hρ i).2.1)
  have hxS (i : ℕ) : x ∈ S i := by
    apply (L12Aux.mem_distBall_iff g x x (hρ i).1).mpr
    rw [g.induced_distance_eq_zero.mpr rfl]
    exact (hρ i).1
  have hTfinite : μ T < ⊤ := distBall_volume_lt_top g μ hμ x hr
  have hV : 0 < V := ENNReal.toReal_pos
    (ne_of_gt (riemannianVolume_distBall_pos g μ hμ x hr)) hTfinite.ne
  have huT : IntegrableOn u T μ := smoothFn_integrableOn_distBall g μ hμ hu x hr
  have hu2 (i : ℕ) : IntegrableOn (fun y => u y ^ 2) (S i) μ :=
    smoothFn_integrableOn_distBall g μ hμ (smoothFn_pow hu 2) x (hρ i).1
  have hbdd : BddAbove (u '' T) := by
    apply ((L12Aux.isCompact_inducedDistance_sublevel g x r).image
      (continuous_of_smoothFn hu)).bddAbove.mono
    apply Set.image_mono
    intro y hy
    exact ((L12Aux.mem_distBall_iff g x y hr).mp hy).le
  have hb : 1 ≤ b := one_le_pow₀ (by norm_num : (1 : ℝ) ≤ 2)
  have hE : 0 ≤ E := by dsimp [E, D]; positivity
  have hstep (i : ℕ) : (sSup (u '' S i)) ^ 2 ≤
      (E / V) * b ^ i * ∫ y in S (i + 1), u y ^ 2 ∂μ := by
    have hloc := hL2 M g hcomplete hK hRic μ hμ u hu hu0 husub x
      (ρ i) (ρ (i + 1)) (hρ i).1 (hρstep i).1
    have hWpos : 0 < μ.real (S (i + 1)) := ENNReal.toReal_pos
      (ne_of_gt (riemannianVolume_distBall_pos g μ hμ x (hρ (i + 1)).1))
      (distBall_volume_lt_top g μ hμ x (hρ (i + 1)).1).ne
    have hVW : V ≤ D * μ.real (S (i + 1)) :=
      interpolation_volume_bound g hcomplete hK hRic μ hμ x hr (i + 1)
    have hinv : 1 / μ.real (S (i + 1)) ≤ D / V := by
      apply (div_le_div_iff₀ hWpos hV).mpr
      simpa using hVW
    have hratio0 : 0 ≤ ρ (i + 1) / (ρ (i + 1) - ρ i) :=
      div_nonneg (hρ (i + 1)).1.le (sub_pos.mpr (hρstep i).1).le
    have hpow := pow_le_pow_left₀ hratio0 (hρstep i).2 N
    have hcoef : A * (ρ (i + 1) / (ρ (i + 1) - ρ i)) ^ N /
        μ.real (S (i + 1)) ≤ (E / V) * b ^ i := by
      calc
        _ = (A * (ρ (i + 1) / (ρ (i + 1) - ρ i)) ^ N) *
            (1 / μ.real (S (i + 1))) := by ring
        _ ≤ (A * ((2 : ℝ) ^ (i + 2)) ^ N) * (D / V) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left hpow hA.le
          · exact hinv
          · positivity
          · positivity
        _ = (E / V) * b ^ i := by
          dsimp [E, b]
          rw [← pow_mul, Nat.add_mul, pow_add, pow_mul, pow_right_comm]
          ring
    exact hloc.trans (mul_le_mul_of_nonneg_right hcoef
      (integral_nonneg (fun y => sq_nonneg (u y))))
  have hpoint := L2_to_L1_interpolation μ u S T hS (fun i => ⟨x, hxS i⟩)
    hST hu0 huT hu2 hbdd (div_nonneg hE hV.le) hb hstep x (hxS 0)
  apply (meanValue_ennreal_iff μ T huT hu0 (hu0 x)
    (mul_nonneg (by dsimp [b]; positivity) hE) hTfinite).mpr
  change u x * V ≤ b * E * ∫ y in T, u y ∂μ
  have hp := mul_le_mul_of_nonneg_right hpoint hV.le
  calc
    u x * V ≤ (b * (E / V) * ∫ y in T, u y ∂μ) * V := hp
    _ = b * E * ∫ y in T, u y ∂μ := by field_simp

end Yau.LeafProofs.L18Aux
