import Yau.LeafProofs.L05ChuResidualSource

noncomputable section

open Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius

namespace Yau.LeafProofs.L05Aux

open Yau.Parabolic Yau.ParabolicCandidates

theorem holderWeight_le_twice_radius_power {n : ℕ} {beta r : ℝ}
    (hb : 0 ≤ beta) {p q : Point n} (hpq : parabolicDistance p q ≤ r) :
    holderWeight beta p q ≤ 2*r^beta := by
  have hx : ‖p.1-q.1‖ ≤ r := (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hpq
  have ht : Real.sqrt |p.2-q.2| ≤ r := (le_add_of_nonneg_left (norm_nonneg _)).trans hpq
  have hs := Real.rpow_le_rpow (norm_nonneg _) hx hb
  have hv := Real.rpow_le_rpow (Real.sqrt_nonneg _) ht hb
  rw [← Real.rpow_div_two_eq_sqrt beta (abs_nonneg _)] at hv
  exact (add_le_add hs hv).trans_eq (by ring)

theorem holderWeight_lower_exponent_near {n : ℕ} {gamma alpha : ℝ}
    (hg : 0 ≤ gamma) (hga : gamma ≤ alpha) {p q : Point n}
    (hpq : parabolicDistance p q ≤ 1) : holderWeight alpha p q ≤ holderWeight gamma p q := by
  have hx : ‖p.1-q.1‖ ≤ 1 := (le_add_of_nonneg_right (Real.sqrt_nonneg _)).trans hpq
  have ht : Real.sqrt |p.2-q.2| ≤ 1 := (le_add_of_nonneg_left (norm_nonneg _)).trans hpq
  have hs := Real.rpow_le_rpow_of_exponent_ge' (norm_nonneg _) hx hg hga
  have hv := Real.rpow_le_rpow_of_exponent_ge' (Real.sqrt_nonneg _) ht hg hga
  rw [← Real.rpow_div_two_eq_sqrt alpha (abs_nonneg _),
    ← Real.rpow_div_two_eq_sqrt gamma (abs_nonneg _)] at hv
  exact add_le_add hs hv

theorem chu_modulus_absorption_radius {omega : ℝ → ℝ} (hm : Modulus omega)
    {eta beta A B C D epsilon : ℝ} (he : 0 < eta) (hb : 0 < beta)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (heps : 0 < epsilon) :
    ∃ rho : ℝ, 0 < rho ∧ rho ≤ 1 ∧ ∀ r : ℝ, 0 ≤ r → r ≤ rho →
      C*omega (A*r^eta+B*r^beta+r)+D*r^beta ≤ epsilon := by
  let s := fun r : ℝ => A*r^eta+B*r^beta+r
  have hr : Tendsto (fun r : ℝ => r) (𝓝[Set.Ici 0] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hre := hr.rpow_const (Or.inr he.le)
  have hrb := hr.rpow_const (Or.inr hb.le)
  simp only [Real.zero_rpow he.ne',Real.zero_rpow hb.ne'] at hre hrb
  have hs : Tendsto s (𝓝[Set.Ici 0] 0) (𝓝 0) := by
    convert! ((hre.const_mul A).add (hrb.const_mul B)).add hr using 1 <;>
      simp only [mul_zero,zero_add]
  have hsw : Tendsto s (𝓝[Set.Ici 0] 0) (𝓝[Set.Ici 0] 0) := by
    apply tendsto_nhdsWithin_iff.mpr
    refine ⟨hs,?_⟩
    filter_upwards [self_mem_nhdsWithin] with r hr0
    exact add_nonneg (add_nonneg (mul_nonneg hA (Real.rpow_nonneg hr0 _))
      (mul_nonneg hB (Real.rpow_nonneg hr0 _))) hr0
  have hsmall : Tendsto (fun r : ℝ => C*omega (s r)+D*r^beta)
      (𝓝[Set.Ici 0] 0) (𝓝 0) := by
    convert! (((hm.2.2.2.comp hsw).const_mul C).add (hrb.const_mul D)) using 1 <;>
      simp only [mul_zero,zero_add]
  obtain ⟨d,hd,hbound⟩ := Metric.tendsto_nhdsWithin_nhds.mp hsmall epsilon heps
  refine ⟨min 1 (d/2),lt_min (by norm_num) (half_pos hd),min_le_left _ _,?_⟩
  intro r hr0 hrho
  have hrd : dist r 0 < d := by
    rw [Real.dist_eq,sub_zero,abs_of_nonneg hr0]
    exact (hrho.trans (min_le_right _ _)).trans_lt (by linarith)
  have hh := hbound (show r ∈ Set.Ici 0 from hr0) hrd
  rw [Real.dist_eq,sub_zero] at hh
  exact (le_abs_self _).trans hh.le

end Yau.LeafProofs.L05Aux
