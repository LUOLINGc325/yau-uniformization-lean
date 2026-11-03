import Yau.Proofs.C07ChartBallMaps
import Yau.Proofs.C07ChartChord
import Yau.Proofs.C07PolygonalPrefixConstant

open scoped Manifold Topology ContDiff unitInterval

noncomputable section

namespace Yau.Proofs.C07PolygonalPrefixAux

open Yau Set C07Aux C07ChartChordAux C07RadialCurveAux D04AtlasGlueAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

def repointCurve {x y x' y' : M.Carrier} (γ : IntegrableCurve g x y)
    (hx : x = x') (hy : y = y') : IntegrableCurve g x' y' :=
  ⟨{ γ.1 with
      start_eq := γ.1.start_eq.trans hx
      finish_eq := γ.1.finish_eq.trans hy }, γ.2⟩

theorem repointCurve_apply {x y x' y' : M.Carrier} (γ : IntegrableCurve g x y)
    (hx : x = x') (hy : y = y') (u : ℝ) :
    (repointCurve γ hx hy).1 u = γ.1 u := rfl

theorem repointCurve_length {x y x' y' : M.Carrier} (γ : IntegrableCurve g x y)
    (hx : x = x') (hy : y = y') :
    curveLength g (repointCurve γ hx hy).1 = curveLength g γ.1 := rfl

set_option maxHeartbeats 800000 in
/-- A stopped chart segment depends continuously on the stopping time.
Before its partition point it is the constant curve at the requested endpoint. -/
theorem exists_segment_family (hg : MetricSmooth g) (H : C(I × I, M.Carrier))
    (N : Set I) (B : ChartBall M) (ti tj : I) (hij : ti ≤ tj)
    (hB : ∀ s : N, ∀ u ∈ Icc ti tj, H (u, s.1) ∈ B.inner)
    (K : Set M.Carrier) (hHK : ∀ t : I, ∀ s : N, H (t, s.1) ∈ K)
    (hBK : chartBallMap B '' Metric.closedBall 0 (2 * B.radius) ⊆ K)
    (o : M.Carrier) (h0 : ∀ s : I, H (0, s) = o) :
    ∃ L : ℝ, 0 ≤ L ∧
      ∃ (γ : ∀ a : I × N,
          IntegrableCurve g (H (min a.1 ti, a.2.1)) (H (min a.1 tj, a.2.1)))
        (P : C(I × (I × N), M.Carrier)),
        (∀ u a, P (u, a) = (γ a).1 u) ∧
        (∀ a, curveLength g (γ a).1 ≤ L) ∧
        (∀ a u, u ∈ Icc (0 : ℝ) 1 → (γ a).1 u ∈ K) ∧
        (∀ s : N, ∀ u ∈ Icc (0 : ℝ) 1, (γ (0, s)).1 u = o) := by
  classical
  let stop : I → I := fun t => max ti (min t tj)
  have hstop : ∀ t, stop t ∈ Icc ti tj :=
    fun t => ⟨le_max_left _ _, max_le hij (min_le_right _ _)⟩
  have hstopc : Continuous stop := continuous_const.max (continuous_id.min continuous_const)
  have houter : ∀ s : N, ∀ u ∈ Icc ti tj, H (u, s.1) ∈ B.outer :=
    fun s u hu => B.core_subset_outer (B.inner_subset_core (hB s u hu))
  let α : I × N → ComplexVector n := fun a => chartBallCoord B (H (ti, a.2.1))
  let β : I × N → ComplexVector n := fun a => chartBallCoord B (H (stop a.1, a.2.1))
  have hαmem : ∀ a, α a ∈ Metric.ball 0 (2 * B.radius) :=
    fun a => chartBallCoord_outer B (houter a.2 ti ⟨le_rfl, hij⟩)
  have hβmem : ∀ a, β a ∈ Metric.ball 0 (2 * B.radius) :=
    fun a => chartBallCoord_outer B (houter a.2 _ (hstop a.1))
  have hα : Continuous α := (chartBallCoord_continuousOn B).comp_continuous
    (H.continuous.comp (continuous_const.prodMk (continuous_subtype_val.comp continuous_snd)))
    (fun a => houter a.2 ti ⟨le_rfl, hij⟩)
  have hβ : Continuous β := (chartBallCoord_continuousOn B).comp_continuous
    (H.continuous.comp ((hstopc.comp continuous_fst).prodMk
      (continuous_subtype_val.comp continuous_snd)))
    (fun a => houter a.2 _ (hstop a.1))
  have hRr : 2 * B.radius < 3 * B.radius := by linarith [B.radius_pos]
  let ρ : ∀ a : I × N, IntegrableCurve g
      (chartBallMap B (α a)) (chartBallMap B (β a)) :=
    fun a => chordIntegrable (k := g) (ψ := chartBallMap B)
      (r := 3 * B.radius) (R := 2 * B.radius)
      hg (chartBallMap_contMDiff B) hRr (hαmem a) (hβmem a)
  let right : I × (I × N) → M.Carrier :=
    fun p => chordPath (chartBallMap B) (α p.2) (β p.2) p.1
  have hright : Continuous right := by
    change Continuous (fun p : I × (I × N) => chartBallMap B
      (α p.2 + radialClamp (p.1 : ℝ) • (β p.2 - α p.2)))
    exact (chartBallMap_contMDiff B).continuousOn.comp_continuous
      ((hα.comp continuous_snd).add
        ((continuous_radialClamp.comp (continuous_subtype_val.comp continuous_fst)).smul
          ((hβ.comp continuous_snd).sub (hα.comp continuous_snd))))
      (fun p => Metric.ball_subset_ball hRr.le
        (chord_point_mem (hαmem p.2) (hβmem p.2) (radialClamp_mem _)))
  have hself : ∀ (u : I) (a : I × N), a.1 = ti → right (u, a) = H (a.1, a.2.1) := by
    intro u a ha
    have hstopi : stop a.1 = ti := by simp only [stop, ha, min_eq_left hij, max_self]
    dsimp [right, α, β]
    rw [hstopi, chordPath_self, chartBallMap_coord B (houter a.2 ti ⟨le_rfl, hij⟩), ha]
  let f : I × (I × N) → M.Carrier := fun p =>
    if p.2.1 ≤ ti then H (p.2.1, p.2.2.1) else right p
  have hf : Continuous f := continuous_if_le continuous_snd.fst continuous_const
    (H.continuous.comp (continuous_snd.fst.prodMk
      (continuous_subtype_val.comp continuous_snd.snd))).continuousOn
    hright.continuousOn (fun p hp => (hself p.1 p.2 hp).symm)
  have hρstart : ∀ a : I × N, chartBallMap B (α a) = H (ti, a.2.1) :=
    fun a => chartBallMap_coord B (houter a.2 ti ⟨le_rfl, hij⟩)
  have hρfinish : ∀ a : I × N, chartBallMap B (β a) = H (stop a.1, a.2.1) :=
    fun a => chartBallMap_coord B (houter a.2 _ (hstop a.1))
  let γ : ∀ a : I × N,
      IntegrableCurve g (H (min a.1 ti, a.2.1)) (H (min a.1 tj, a.2.1)) := fun a =>
    if h : a.1 ≤ ti then
      repointCurve (constantIntegrable g (H (a.1, a.2.1)))
        (by rw [min_eq_left h]) (by rw [min_eq_left (h.trans hij)])
    else
      repointCurve (ρ a)
        (by rw [min_eq_right (le_of_not_ge h)]; exact hρstart a)
        (by
          rw [hρfinish]
          dsimp only [stop]
          rw [max_eq_right (le_min (le_of_not_ge h) hij)])
  obtain ⟨C, hC, hlen⟩ := exists_chord_length_bound hg (chartBallMap_contMDiff B) hRr
  let L := Real.sqrt (2 * C) * (4 * B.radius)
  have hL : 0 ≤ L := mul_nonneg (Real.sqrt_nonneg _) (by linarith [B.radius_pos])
  refine ⟨L, hL, γ, ⟨f, hf⟩, ?_, ?_, ?_, ?_⟩
  · intro u a
    dsimp [f, γ]
    split_ifs with h
    · rfl
    · exact (chordIntegrable_apply hg (chartBallMap_contMDiff B) hRr (hαmem a) (hβmem a) u).symm
  · intro a
    dsimp only [γ]
    split_ifs with h
    · rw [repointCurve_length, constant_length]
      exact hL
    · rw [repointCurve_length]
      refine (hlen (α a) (hαmem a) (β a) (hβmem a)).trans ?_
      apply mul_le_mul_of_nonneg_left _ (Real.sqrt_nonneg _)
      have ha : ‖α a‖ < 2 * B.radius := by simpa only [Metric.mem_ball, dist_zero_right] using hαmem a
      have hb : ‖β a‖ < 2 * B.radius := by simpa only [Metric.mem_ball, dist_zero_right] using hβmem a
      exact (norm_sub_le _ _).trans (by linarith)
  · intro a u hu
    dsimp only [γ]
    split_ifs with h
    · exact hHK a.1 a.2
    · exact hBK (chordPath_mem_image (chartBallMap B) (hαmem a) (hβmem a) u)
  · intro s u hu
    have hi : (0 : I) ≤ ti := ti.2.1
    simp only [γ, dif_pos hi, repointCurve_apply, constantIntegrable, constantPiecewise]
    exact h0 s.1

end Yau.Proofs.C07PolygonalPrefixAux
