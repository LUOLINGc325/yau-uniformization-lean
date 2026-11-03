import Yau.LeafProofs.L22Uniform
import Yau.LeafProofs.L22Circle
import Yau.LeafProofs.L22Convolution
import Yau.LeafProofs.L22LeviCalculus

noncomputable section

open scoped Topology ContDiff Manifold Matrix ComplexOrder
open Set Filter

namespace Yau.LeafProofs.L22Aux

variable {n : ℕ} {M : ComplexManifold n}

/-- Original classical strictifiers can be restricted to concentric genuine
coordinate balls with a uniform positive quadratic lower bound. -/
theorem exists_classical_strictifier_ball {u : M.Carrier → ℝ}
    (hu : LeafCandidates.ClassicalStrictPsh u) (p : M.Carrier) :
    ∃ (r lam : ℝ) (τ : ComplexVector n → ℝ), 0 < r ∧ 0 < lam ∧
      Metric.closedBall (chartPt p p) (3 * r) ⊆ chartTarget p ∧
      ContDiffOn ℝ ∞ τ (Metric.ball (chartPt p p) (3 * r)) ∧
      LeafCandidates.ComplexLinePshOn (Metric.ball (chartPt p p) (3 * r))
        (fun z => inChart p u z - τ z) ∧
      ∀ z ∈ Metric.closedBall (chartPt p p) (2 * r), ∀ v,
        lam * ‖v‖ ^ 2 ≤ complexLeviQuadratic τ z v := by
  obtain ⟨O, hO, hp, hchart, τ, hτ, hpos, hpsh⟩ := hu.2 p
  obtain ⟨r₀, lam, hr₀, hlam, hlower⟩ :=
    exists_uniform_levi_lower_bound (hτ.contDiffAt (hO.mem_nhds hp)) hpos
  obtain ⟨R, hR, hRO⟩ := Metric.isOpen_iff.mp (hO.inter Metric.isOpen_ball)
    (chartPt p p) ⟨hp, Metric.mem_ball_self hr₀⟩
  have hball : Metric.closedBall (chartPt p p) (3 * (R / 4)) ⊆
      O ∩ Metric.ball (chartPt p p) r₀ :=
    (Metric.closedBall_subset_ball (by linarith : 3 * (R / 4) < R)).trans hRO
  refine ⟨R / 4, lam, τ, by positivity, hlam,
    hball.trans (inter_subset_left.trans hchart),
    hτ.mono (Metric.ball_subset_closedBall.trans (hball.trans inter_subset_left)),
    complexLinePshOn_mono hpsh
      (Metric.ball_subset_closedBall.trans (hball.trans inter_subset_left)), ?_⟩
  intro z hz v
  exact hlower z ((hball (Metric.closedBall_subset_closedBall (by linarith) hz)).2) v

/-- A small smooth bump perturbation of the local strictifier and a genuine
psh convolution produce the quantitative local branches used in patching. -/
theorem exists_coordinate_strict_branch
    (c : ComplexVector n) {r lam : ℝ} (hr : 0 < r) (hlam : 0 < lam)
    (f τ χ ε : ComplexVector n → ℝ)
    (hτ : ContDiffOn ℝ ∞ τ (Metric.ball c (3 * r)))
    (hχ : ContDiffOn ℝ ∞ χ (Metric.ball c (3 * r)))
    (hpsh : LeafCandidates.ComplexLinePshOn (Metric.ball c (3 * r)) (fun z => f z - τ z))
    (hlower : ∀ z ∈ Metric.closedBall c (2 * r), ∀ v,
      lam * ‖v‖ ^ 2 ≤ complexLeviQuadratic τ z v)
    (hε : ContinuousOn ε (Metric.closedBall c (2 * r)))
    (hεpos : ∀ z ∈ Metric.closedBall c (2 * r), 0 < ε z)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKr : K ⊆ Metric.ball c r) :
    ∃ (t : ℝ) (W : Set (ComplexVector n)) (h : ComplexVector n → ℝ),
      0 < t ∧ IsOpen W ∧ K ⊆ W ∧ W ⊆ Metric.ball c (2 * r) ∧
      ContDiffOn ℝ ∞ h W ∧ (∀ z ∈ W, (leviC h z).PosDef) ∧
      (∀ z ∈ W, |h z - f z - t * (2 * χ z - 1)| < t / 4) ∧
      ∀ z ∈ W, 2 * t < ε z := by
  let b : ComplexVector n → ℝ := fun z => 2 * χ z - 1
  have hb : ContDiffOn ℝ ∞ b (Metric.ball c (3 * r)) :=
    (contDiffOn_const.mul hχ).sub contDiffOn_const
  have hbig : Metric.closedBall c (2 * r) ⊆ Metric.ball c (3 * r) :=
    Metric.closedBall_subset_ball (by linarith)
  obtain ⟨C, hC, hCbound⟩ := exists_uniform_levi_bound_on_compact Metric.isOpen_ball hb
    (isCompact_closedBall c (2 * r)) hbig
  obtain ⟨m, hm, hmlower⟩ := (isCompact_closedBall c (2 * r)).exists_forall_le' hε hεpos
  let t : ℝ := min (lam / (2 * (C + 1))) (m / 4)
  have ht : 0 < t := lt_min (by positivity) (by positivity)
  have htC : t * C ≤ lam / 2 := by
    have h := (le_div_iff₀ (by positivity : 0 < 2 * (C + 1))).mp
      (min_le_left (lam / (2 * (C + 1))) (m / 4))
    nlinarith
  have htm : 2 * t < m := by
    have h := min_le_right (lam / (2 * (C + 1))) (m / 4)
    dsimp only [t]
    linarith
  have hKbig : K ⊆ Metric.ball c (3 * r) :=
    hKr.trans (Metric.ball_subset_ball (by linarith))
  obtain ⟨V, a, hV, hKV, hVbig, ha, haps, herror⟩ :=
    exists_smooth_psh_approx_near_compact Metric.isOpen_ball hpsh hK hKbig
      (by positivity : 0 < t / 4)
  let W := V ∩ Metric.ball c (2 * r)
  let h : ComplexVector n → ℝ := fun z => (τ z + a z) + t * b z
  have hWbig : W ⊆ Metric.ball c (3 * r) :=
    inter_subset_right.trans Metric.ball_subset_closedBall |>.trans hbig
  have hhs : ContDiffOn ℝ ∞ h W :=
    ((hτ.mono hWbig).add ha.contDiffOn).add (contDiffOn_const.mul (hb.mono hWbig))
  refine ⟨t, W, h, ht, hV.inter Metric.isOpen_ball,
    (fun z hz => ⟨hKV hz, Metric.ball_subset_ball (by linarith) (hKr hz)⟩),
    inter_subset_right, hhs, ?_, ?_, ?_⟩
  · intro z hz
    have hzbig := hWbig hz
    have hτz : ContDiffAt ℝ 2 τ z := (hτ.contDiffAt (Metric.isOpen_ball.mem_nhds hzbig)).of_le (by simp)
    have haz : ContDiffAt ℝ 2 a z := ha.contDiffAt.of_le (by simp)
    have hbz : ContDiffAt ℝ 2 b z := (hb.contDiffAt (Metric.isOpen_ball.mem_nhds hzbig)).of_le (by simp)
    apply (leviC_posDef_iff ((hτz.add haz).add (contDiffAt_const.mul hbz))).mpr
    intro v hv
    have hqeq : complexLeviQuadratic h z v = complexLeviQuadratic τ z v +
        complexLeviQuadratic a z v + t * complexLeviQuadratic b z v := by
      rw [complexLeviQuadratic_add (hτz.add haz) (contDiffAt_const.mul hbz),
        complexLeviQuadratic_add hτz haz, complexLeviQuadratic_const_mul hbz]
    rw [hqeq]
    have hτlower := hlower z (Metric.ball_subset_closedBall hz.2) v
    have habove := (leviC_posSemidef_iff haz).mp
      (leviC_posSemidef_of_smooth_psh hV haps ha hz.1) v
    have hbbelow := (abs_le.mp (hCbound z (Metric.ball_subset_closedBall hz.2) v)).1
    have hnorm : 0 < ‖v‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hv)
    nlinarith [mul_le_mul_of_nonneg_left hbbelow ht.le,
      mul_le_mul_of_nonneg_right htC hnorm.le]
  · intro z hz
    have heq : h z - f z - t * (2 * χ z - 1) = a z - (f z - τ z) := by dsimp [h, b]; ring
    rw [heq]
    exact herror z hz.1
  · intro z hz
    exact htm.trans_le (hmlower z (Metric.ball_subset_closedBall hz.2))

end Yau.LeafProofs.L22Aux
