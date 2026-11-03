import Yau.Blueprint.Stages

/-! Centered image radii and the explicit strict exponential gain. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.Blueprint.U03Proof

variable {n : ℕ}

theorem proper_open_radius
    (Ω : Set (ComplexVector n)) (hopen : IsOpen Ω)
    (hzero : (0 : ComplexVector n) ∈ Ω) (hproper : Ω ≠ Set.univ) :
    let A := {R : ℝ | 0 < R ∧ Metric.ball (0 : ComplexVector n) R ⊆ Ω}
    A.Nonempty ∧ BddAbove A ∧ 0 < centeredImageRadius Ω ∧
      (∀ r : ℝ, 0 < r → r < centeredImageRadius Ω →
        Metric.closedBall (0 : ComplexVector n) r ⊆ Ω) := by
  classical
  let A := {R : ℝ | 0 < R ∧ Metric.ball (0 : ComplexVector n) R ⊆ Ω}
  obtain ⟨r0, hr0, hball0⟩ := Metric.isOpen_iff.mp hopen 0 hzero
  have hAne : A.Nonempty := ⟨r0, hr0, hball0⟩
  obtain ⟨z0, hz0⟩ : ∃ z0 : ComplexVector n, z0 ∉ Ω := by
    by_contra h
    apply hproper
    exact Set.eq_univ_iff_forall.mpr (by simpa using h)
  have hAbdd : BddAbove A := by
    refine ⟨‖z0‖, ?_⟩
    intro R hR
    by_contra hle
    have hzball : z0 ∈ Metric.ball (0 : ComplexVector n) R := by
      simpa only [Metric.mem_ball, dist_zero_right] using lt_of_not_ge hle
    exact hz0 (hR.2 hzball)
  refine ⟨hAne, hAbdd, hr0.trans_le (le_csSup hAbdd ⟨hr0, hball0⟩), ?_⟩
  intro r _ hr
  obtain ⟨R, hR, hrR⟩ := exists_lt_of_lt_csSup hAne hr
  intro z hz
  apply hR.2
  have hzn : ‖z‖ ≤ r := by
    simpa only [Metric.mem_closedBall, dist_zero_right] using hz
  simpa only [Metric.mem_ball, dist_zero_right] using hzn.trans_lt hrR

theorem radii_around {R D sigma gamma : ℝ}
    (hR : 0 < R) (hD : 0 < D) (hgap : gamma < sigma / 2) :
    ∃ R1 R2 : ℝ, 0 < R1 ∧ R1 < R ∧ R < R2 ∧
      D * Real.log (R2 / R1) < sigma / 2 - gamma := by
  let a : ℝ := (sigma / 2 - gamma) / (4 * D)
  let q : ℝ := Real.exp a
  have hag : 0 < sigma / 2 - gamma := sub_pos.mpr hgap
  have ha : 0 < a := div_pos hag (by positivity)
  have hq : 1 < q := Real.one_lt_exp_iff.mpr ha
  have hqpos : 0 < q := zero_lt_one.trans hq
  refine ⟨R / q, R * q, div_pos hR hqpos, ?_, ?_, ?_⟩
  · exact div_lt_self hR hq
  · nlinarith
  · have heq : R * q / (R / q) = q ^ 2 := by
      field_simp [ne_of_gt hR, ne_of_gt hqpos]
      <;> ring
    have hlogq : Real.log q = a := Real.log_exp a
    rw [heq, Real.log_pow, hlogq]
    change D * (2 * ((sigma / 2 - gamma) / (4 * D))) < sigma / 2 - gamma
    have heq2 : D * (2 * ((sigma / 2 - gamma) / (4 * D))) =
        (sigma / 2 - gamma) / 2 := by
      field_simp [ne_of_gt hD]
      <;> ring
    rw [heq2]
    linarith

theorem power_mul_exp_lt {m : ℕ} {D s sigma gamma R1 R2 : ℝ}
    (_hD : 0 < D) (hs : 0 < s) (hR1 : 0 < R1) (hR12 : R1 < R2)
    (hmdeg : (m : ℝ) ≤ D * s)
    (hratio : D * Real.log (R2 / R1) < sigma / 2 - gamma) :
    (R2 / R1) ^ m * Real.exp (-(sigma / 2) * s) <
      Real.exp (-gamma * s) := by
  have hq : 1 < R2 / R1 := (one_lt_div hR1).2 hR12
  have hqpos : 0 < R2 / R1 := zero_lt_one.trans hq
  have hlog : 0 ≤ Real.log (R2 / R1) := Real.log_nonneg hq.le
  have hdeg := mul_le_mul_of_nonneg_right hmdeg hlog
  have hstrict := mul_lt_mul_of_pos_right hratio hs
  have hexp : (m : ℝ) * Real.log (R2 / R1) + -(sigma / 2) * s < -gamma * s := by
    nlinarith
  have hpow : (R2 / R1) ^ m = Real.exp ((m : ℝ) * Real.log (R2 / R1)) := by
    rw [← Real.log_pow, Real.exp_log (pow_pos hqpos m)]
  rw [hpow, ← Real.exp_add]
  exact Real.exp_lt_exp.mpr hexp

end Yau.Blueprint.U03Proof
