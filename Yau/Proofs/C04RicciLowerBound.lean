import Yau.Proofs.C04DualMetricBounds
import Yau.Proofs.C04DualRayleigh
import Yau.Proofs.C04ClockSecant
import Yau.Proofs.C04ClockInverse

/-! The genuine Ricci minimum at the original clock's smaller level. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter Set

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

theorem ricci_lower_bound (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) (hCharts : UniformCharts X h) (hStatic : StaticDistortion X) :
    ∃ a b, 0 < a ∧ a < 1 ∧ 0 < b ∧
      ∃ T, ∀ t u, T ≤ t → 0 ≤ u → ρ o u = a * ρ o t →
        b * clockSpeed o h u ≤ ricciMin o h t := by
  obtain ⟨c, hc, T₀, hsecant⟩ := dualLog_secant_lower X o h U P ρ hf hH hCharts hStatic
  let a := min (1 / 2 : ℝ) (c / 8)
  have ha : 0 < a := lt_min (by norm_num) (by positivity)
  have ha1 : a < 1 := (min_le_left _ _).trans_lt (by norm_num)
  have hac : a ≤ c / 8 := min_le_right _ _
  let b := c - 2 * a
  have hb : 0 < b := by dsimp only [b]; linarith
  obtain ⟨B, hB⟩ := (tendsto_atTop_atTop.1 (rho_tendsto_atTop X o h U P ρ hf hH)) 1
  let A := max 1 (max T₀ B)
  have hA : 0 < A := zero_lt_one.trans_le (le_max_left _ _)
  have hAT : T₀ ≤ A := (le_max_left _ _).trans (le_max_right _ _)
  have hsA : 0 < ρ o A := zero_lt_one.trans_le
    (hB A ((le_max_right _ _).trans (le_max_right _ _)))
  obtain ⟨B', hB'⟩ := (tendsto_atTop_atTop.1 (rho_tendsto_atTop X o h U P ρ hf hH)) (ρ o A / a)
  refine ⟨a, b, ha, ha1, hb, max A B', ?_⟩
  intro t u ht hu hclock
  have htA : A ≤ t := (le_max_left _ _).trans ht
  have htpos : 0 < t := hA.trans_le htA
  have has : ρ o A ≤ a * ρ o t := by
    have hh := hB' t ((le_max_right _ _).trans ht)
    exact (div_le_iff₀ ha).mp hh |>.trans_eq (mul_comm _ _)
  have hstrict := rho_strictMonoOn_nonneg X o h U P ρ hf hH
  have huA : A ≤ u := by
    by_contra hn
    have hh := hstrict hu hA.le (lt_of_not_ge hn)
    rw [hclock] at hh
    linarith
  have hup : 0 < u := hA.trans_le huA
  have hs : 0 < ρ o t := hsA.trans_le (hstrict.monotoneOn hA.le htpos.le htA)
  have hsu : 0 < ρ o u := by rw [hclock]; exact mul_pos ha hs
  have hut : u ≤ t := by
    by_contra hn
    have hh := hstrict htpos.le hu (lt_of_not_ge hn)
    rw [hclock] at hh
    nlinarith
  have hq : 0 < clockSpeed o h u := mul_pos hup (scalar_pos X o h hH hu o)
  apply ricciMin_lower_of_dual_rates X o h t
  intro v hv
  have hlower : b * ρ o t ≤ dualLog h o v t - dualLog h o v u := by
    have hh := hsecant t u (hAT.trans htA) (hAT.trans huA) v hv
    rw [hclock] at hh
    dsimp only [b]
    nlinarith
  have hlog := dualLog_secant X o h U P ρ hf hH o v hv hup hut
  have hinterval := clock_logarithmic_interval X o h U P ρ hf hH hup hut
  exact endpoint_rate_lower b (ρ o t) (clockSpeed o h u) (dualClockRate h o v t)
    (Real.log t - Real.log u) (dualLog h o v t - dualLog h o v u) hs hq
    (dualClockRate_nonneg X o h hH o htpos v hv) hlower hlog
    (hinterval.trans (by linarith))

end Yau.Proofs.C04Aux
