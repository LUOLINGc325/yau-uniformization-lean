import Yau.LeafProofs.L21GraphConvergence
import Yau.LeafProofs.L21FlatEnergy

/-! Strong limits in the genuine complex L² space, including continuity of
the compact test pairings used to identify distributional derivatives. -/

open MeasureTheory Filter
open scoped Topology
noncomputable section
namespace Yau.LeafProofs.L21Aux

variable {E : Type*} [MeasurableSpace E] {μ : Measure E}

theorem complex_toLp_norm_sq (f : E → ℂ) (hf : MemLp f 2 μ) :
    ‖hf.toLp f‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 ∂μ := by
  rw [← real_inner_self_eq_norm_sq, L2.inner_def]
  apply integral_congr_ae
  filter_upwards [hf.coeFn_toLp] with x hx
  simp only [hx, real_inner_self_eq_norm_sq]

theorem complex_toLp_sub_norm_sq (f g : E → ℂ) (hf : MemLp f 2 μ) (hg : MemLp g 2 μ) :
    ‖hf.toLp f - hg.toLp g‖ ^ 2 = ∫ x, ‖f x - g x‖ ^ 2 ∂μ := by
  rw [← MemLp.toLp_sub hf hg, complex_toLp_norm_sq]
  rfl

theorem complex_toLp_tendsto_of_integral_norm_sq
    {ι : Type*} {l : Filter ι} (f : ι → E → ℂ) (g : E → ℂ)
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun j => (hf j).toLp (f j)) l (𝓝 (hg.toLp g)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hs : Tendsto (fun j => ‖(hf j).toLp (f j) - hg.toLp g‖ ^ 2) l (𝓝 0) := by
    simpa only [complex_toLp_sub_norm_sq] using ht
  simpa only [Real.sqrt_sq_eq_abs, abs_norm, Real.sqrt_zero] using hs.sqrt

theorem complex_integral_norm_sq_tendsto_of_toLp_tendsto
    {ι : Type*} {l : Filter ι} (f : ι → E → ℂ) (g : E → ℂ)
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun j => (hf j).toLp (f j)) l (𝓝 (hg.toLp g))) :
    Tendsto (fun j => ∫ x, ‖f j x - g x‖ ^ 2 ∂μ) l (𝓝 0) := by
  simpa only [complex_toLp_sub_norm_sq, zero_pow (by decide : 2 ≠ 0)] using
    (tendsto_iff_norm_sub_tendsto_zero.mp ht).pow 2

theorem complex_pair_norm_sq_tendsto_zero (f : ℕ → E → ℂ) (g : E → ℂ)
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ^ 2 ∂μ) atTop (𝓝 0)) :
    Tendsto (fun p : ℕ × ℕ => ∫ x, ‖f p.1 x - f p.2 x‖ ^ 2 ∂μ) atTop (𝓝 0) := by
  have hfst : Tendsto (Prod.fst : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_fst
  have hsnd : Tendsto (Prod.snd : ℕ × ℕ → ℕ) atTop atTop := by
    rw [← prod_atTop_atTop_eq]
    exact tendsto_snd
  have hh := complex_toLp_tendsto_of_integral_norm_sq f g hf hg ht
  have hh2 := ((hh.comp hfst).sub (hh.comp hsnd)).norm.pow 2
  simpa only [sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    Function.comp_apply, complex_toLp_sub_norm_sq] using hh2

theorem complex_integral_norm_sq_tendsto {ι : Type*} {l : Filter ι}
    (f : ι → E → ℂ) (g : E → ℂ)
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ)
    (ht : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun j => ∫ x, ‖f j x‖ ^ 2 ∂μ) l (𝓝 (∫ x, ‖g x‖ ^ 2 ∂μ)) := by
  simpa only [complex_toLp_norm_sq] using
    (complex_toLp_tendsto_of_integral_norm_sq f g hf hg ht).norm.pow 2

theorem complex_cauchySeq_toLp_of_pair_norm_sq (f : ℕ → E → ℂ)
    (hf : ∀ j, MemLp (f j) 2 μ)
    (ht : Tendsto (fun p : ℕ × ℕ => ∫ x, ‖f p.1 x - f p.2 x‖ ^ 2 ∂μ)
      atTop (𝓝 0)) : CauchySeq (fun j => (hf j).toLp (f j)) := by
  apply Metric.cauchySeq_iff.mpr
  intro ε hε
  obtain ⟨N, hN⟩ := eventually_atTop_prod_self'.mp
    (ht.eventually (gt_mem_nhds (sq_pos_of_pos hε)))
  refine ⟨N, fun m hm k hk => ?_⟩
  have hh := hN m hm k hk
  rw [← complex_toLp_sub_norm_sq _ _ (hf m) (hf k), ← dist_eq_norm] at hh
  nlinarith [dist_nonneg (x := (hf m).toLp (f m)) (y := (hf k).toLp (f k))]

theorem complex_integral_pair_tendsto {ι : Type*} {l : Filter ι}
    (f : ι → E → ℂ) (g h : E → ℂ)
    (hf : ∀ j, MemLp (f j) 2 μ) (hg : MemLp g 2 μ) (hh : MemLp h 2 μ)
    (ht : Tendsto (fun j => ∫ x, ‖f j x - g x‖ ^ 2 ∂μ) l (𝓝 0)) :
    Tendsto (fun j => ∫ x, star (h x) * f j x ∂μ) l
      (𝓝 (∫ x, star (h x) * g x ∂μ)) := by
  have hn := complex_toLp_tendsto_of_integral_norm_sq f g hf hg ht
  have hi := tendsto_const_nhds.inner hn (𝕜 := ℂ) (x := hh.toLp h)
  have heq (q : E → ℂ) (hq : MemLp q 2 μ) :
      inner ℂ (hh.toLp h) (hq.toLp q) = ∫ x, star (h x) * q x ∂μ := by
    rw [L2.inner_def]
    apply integral_congr_ae
    filter_upwards [hh.coeFn_toLp, hq.coeFn_toLp] with x hx hqx
    simp only [hx, hqx]
    exact RCLike.inner_apply' _ _
  simpa only [heq] using hi

end Yau.LeafProofs.L21Aux
