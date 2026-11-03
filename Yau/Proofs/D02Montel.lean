import Yau.Proofs.D02NormalFamily

/-! Bounded holomorphic maps into a finite-dimensional target have one
locally uniformly convergent increasing extraction. Equicontinuity is
proved by the Schwarz lemma on actual interior discs. -/

open scoped Topology
open Filter

noncomputable section
namespace Yau.NodeProofs.D02Aux

variable {H : Type*} [NormedAddCommGroup H] [NormedSpace ℂ H] [CompleteSpace H] [ProperSpace H]

/-- The same global bound gives equicontinuity at every interior point. -/
theorem bounded_holomorphic_discs_equicontinuous
    (fs : ℕ → ℂ → H) (hf : ∀ j, DifferentiableOn ℂ (fs j) (Metric.ball 0 1))
    (B : ℝ) (hb : ∀ j z, z ∈ Metric.ball (0 : ℂ) 1 → ‖fs j z‖ ≤ B) :
    Equicontinuous (fun j (z : Metric.ball (0 : ℂ) 1) => fs j z) := by
  intro x
  apply Metric.equicontinuousAt_iff.mpr
  intro ε hε
  let C := max B 0 + 1
  have hC : 0 < C := by dsimp [C]; linarith [le_max_right B 0]
  have hbound (j : ℕ) (z : ℂ) (hz : z ∈ Metric.ball (0 : ℂ) 1) : ‖fs j z‖ ≤ C :=
    (hb j z hz).trans (by dsimp [C]; linarith [le_max_left B 0])
  let r := 1 - ‖(x : ℂ)‖
  have hr : 0 < r := by
    have hx : ‖(x : ℂ)‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using x.2
    dsimp [r]
    linarith
  have hball : Metric.ball (x : ℂ) r ⊆ Metric.ball (0 : ℂ) 1 := by
    intro z hz
    have hdist : dist z (x : ℂ) < r := hz
    have htriangle := dist_triangle z (x : ℂ) 0
    simp only [dist_zero_right] at htriangle
    rw [Metric.mem_ball, dist_zero_right]
    dsimp [r] at hdist
    linarith
  let L := 2 * C / r
  have hL : 0 ≤ L := (div_pos (by positivity) hr).le
  refine ⟨min r (ε / (L + 1)), lt_min hr (div_pos hε (by linarith)), ?_⟩
  intro y hxy j
  have hdy : dist (y : ℂ) (x : ℂ) < min r (ε / (L + 1)) := hxy
  have hyr : (y : ℂ) ∈ Metric.ball (x : ℂ) r := hdy.trans_le (min_le_left _ _)
  have hmap : Set.MapsTo (fs j) (Metric.ball (x : ℂ) r)
      (Metric.closedBall (fs j x) (2 * C)) := by
    intro z hz
    change dist (fs j z) (fs j x) ≤ 2 * C
    calc
      dist (fs j z) (fs j x) ≤ dist (fs j z) 0 + dist 0 (fs j x) := dist_triangle _ _ _
      _ = ‖fs j z‖ + ‖fs j x‖ := by simp only [dist_zero_right, dist_zero_left]
      _ ≤ 2 * C := by linarith [hbound j z (hball hz), hbound j x x.2]
  have hs := Complex.dist_le_div_mul_dist_of_mapsTo_ball ((hf j).mono hball) hmap hyr
  have hsmall : (L + 1) * dist (y : ℂ) (x : ℂ) < ε := by
    simpa only [mul_comm] using
      (lt_div_iff₀ (by linarith : 0 < L + 1)).mp (hdy.trans_le (min_le_right _ _))
  change dist (fs j x) (fs j y) < ε
  rw [dist_comm]
  exact hs.trans_lt (by change L * dist (y : ℂ) (x : ℂ) < ε; nlinarith [show 0 ≤ dist (y : ℂ) (x : ℂ) from dist_nonneg])

/-- Vector Montel, with one extraction and genuine holomorphic limit on Δ. -/
theorem bounded_holomorphic_discs_subsequence
    (fs : ℕ → ℂ → H) (hf : ∀ j, DifferentiableOn ℂ (fs j) (Metric.ball 0 1))
    (B : ℝ) (hb : ∀ j z, z ∈ Metric.ball (0 : ℂ) 1 → ‖fs j z‖ ≤ B) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ f : ℂ → H,
      DifferentiableOn ℂ f (Metric.ball 0 1) ∧
      TendstoLocallyUniformlyOn (fun j => fs (φ j)) f atTop (Metric.ball 0 1) := by
  classical
  let D := Metric.ball (0 : ℂ) 1
  letI : LocallyCompactSpace D := Metric.isOpen_ball.locallyCompactSpace
  let Fs (j : ℕ) : C(D, H) := ⟨fun z => fs j z, (hf j).continuousOn.domRestrict⟩
  have heq : Equicontinuous (fun j (z : D) => Fs j z) :=
    bounded_holomorphic_discs_equicontinuous fs hf B hb
  obtain ⟨φ, hφ, fc, hc⟩ := continuousFamily_subsequence_uniformOn_compacts Fs
    (fun K _ => heq.equicontinuousOn K) (fun z =>
      ⟨Metric.closedBall 0 B, isCompact_closedBall _ _, fun j => by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hb j (z : ℂ) z.2⟩)
  let f : ℂ → H := fun z => if hz : z ∈ D then fc ⟨z, hz⟩ else 0
  have hloc : TendstoLocallyUniformlyOn (fun j => fs (φ j)) f atTop D := by
    apply (tendstoLocallyUniformlyOn_iff_forall_isCompact Metric.isOpen_ball).mpr
    intro K hKD hK
    have hK' : IsCompact ((Subtype.val : D → ℂ) ⁻¹' K) :=
      Topology.IsInducing.subtypeVal.isCompact_preimage' hK
        (by simpa only [Subtype.range_coe] using hKD)
    have hh := hc ((Subtype.val : D → ℂ) ⁻¹' K) hK'
    rw [Metric.tendstoUniformlyOn_iff] at hh ⊢
    intro ε hε
    filter_upwards [hh ε hε] with j hj
    intro z hz
    have he : dist (fc ⟨z, hKD hz⟩) (fs (φ j) z) < ε := hj ⟨z, hKD hz⟩ hz
    have hfz : f z = fc ⟨z, hKD hz⟩ := by
      dsimp only [f]
      exact dite_eq_left (hKD hz)
    rw [hfz]
    exact he
  exact ⟨φ, hφ, f, hloc.differentiableOn (Eventually.of_forall fun j => hf (φ j))
    Metric.isOpen_ball, hloc⟩

end Yau.NodeProofs.D02Aux
