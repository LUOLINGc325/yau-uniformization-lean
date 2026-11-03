import Yau.Proofs.C04RescaledTubePathLength
import Yau.Proofs.C04RescaledTubeFirstCrossing

/-! A current-metric ball cannot escape a fixed central ball while the
central metric is bounded by the current metric there. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem central_ball_first_exit (g k : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k) (o p : M.Carrier)
    {r e c : ℝ} (hr : 0 < r) (he : 0 < e) (hc : 0 < c)
    (hsmall : Real.sqrt c * e < 1) (hp : p ∈ distBall g o r)
    (hcmp : ∀ x ∈ distBall g o (r + 2),
      HermLE (gMat g x) ((c : ℂ) • gMat k x)) :
    distBall k p e ⊆ distBall g o (r + 1) := by
  intro x hx
  have hpx := (L23Aux.mem_distBall_iff k p x he).1 hx
  have hop := (L23Aux.mem_distBall_iff g o p hr).1 hp
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  obtain ⟨f, hf0, hf1, hf, hlen⟩ := exists_short_smooth_path k hk p x hpx
  let F : ℝ → ℝ := fun t => inducedDistance g o (f t)
  have hF : Continuous F := (L23Aux.continuous_distFrom g hg o).comp hf.continuous
  apply (L23Aux.mem_distBall_iff g o x (by linarith : 0 < r + 1)).2
  by_contra hn
  have hxlarge : r + 1 ≤ inducedDistance g o x := le_of_not_gt hn
  obtain ⟨t, ht, hFt, hbefore⟩ := continuous_first_crossing hF
    (show F 0 < r + 1 by dsimp [F]; rw [hf0]; linarith)
    (show r + 1 ≤ F 1 by simpa only [F, hf1] using hxlarge)
  have hlocal : ∀ u ∈ Set.Icc (0 : ℝ) t,
      HermLE (gMat g (f u)) ((c : ℂ) • gMat k (f u)) := by
    intro u hu
    apply hcmp
    apply (L23Aux.mem_distBall_iff g o (f u) (by linarith : 0 < r + 2)).2
    have hh := hbefore u hu
    change inducedDistance g o (f u) ≤ r + 1 at hh
    linarith
  have hd := distance_le_fieldPathLength g hg f ht.1
    (hf.contMDiffOn.mono (Set.Icc_subset_Icc le_rfl ht.2))
  have hcomp := fieldPathLength_le g k f 0 t c hc.le hlocal
  have hsub := fieldPathLength_mono k f (a := 0) (b := t) (A := 0) (B := 1)
    le_rfl ht.2
  have hmul := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_pos.2 hsq).ne' ENNReal.ofReal_ne_top hlen
  have hdist : ENNReal.ofReal (inducedDistance g (f 0) (f t)) < ENNReal.ofReal 1 := by
    calc
      _ ≤ fieldPathLength g f 0 t := hd
      _ ≤ ENNReal.ofReal (Real.sqrt c) * fieldPathLength k f 0 t := hcomp
      _ ≤ ENNReal.ofReal (Real.sqrt c) * fieldPathLength k f 0 1 := mul_le_mul' le_rfl hsub
      _ < ENNReal.ofReal (Real.sqrt c) * ENNReal.ofReal e := hmul
      _ = ENNReal.ofReal (Real.sqrt c * e) := (ENNReal.ofReal_mul hsq.le).symm
      _ < ENNReal.ofReal 1 := (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2 hsmall
  have hreal := (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).1 hdist
  rw [hf0] at hreal
  have htri := L23Aux.inducedDistance_triangle g hg o p (f t)
  change inducedDistance g o (f t) = r + 1 at hFt
  linarith

end Yau.Proofs.C04RescaledTubeAux
