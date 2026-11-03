import Yau.Proofs.C04RescaledTubeFirstExit

/-! Local metric comparison traps the whole short path and then compares
balls measured in two current metrics. -/
noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter
namespace Yau.Proofs.C04RescaledTubeAux
open Yau Blueprint LeafProofs
variable {n : ℕ} {M : ComplexManifold n}

theorem short_path_stays_central (g k : HermitianField M)
    (hg : MetricSmooth g) (o p : M.Carrier) {r e c : ℝ}
    (hr : 0 < r) (hc : 0 < c) (hsmall : Real.sqrt c * e < 1)
    (hp : p ∈ distBall g o r)
    (hcmp : ∀ x ∈ distBall g o (r + 2),
      HermLE (gMat g x) ((c : ℂ) • gMat k x))
    (f : ℝ → M.Carrier) (hf0 : f 0 = p)
    (hf : ContMDiff 𝓘(ℝ, ℝ) 𝓘(ℝ, ComplexVector n) 1 f)
    (hlen : fieldPathLength k f 0 1 < ENNReal.ofReal e) :
    ∀ T ∈ Set.Icc (0 : ℝ) 1, f T ∈ distBall g o (r + 1) := by
  intro T hT
  have hop := (L23Aux.mem_distBall_iff g o p hr).1 hp
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hc
  let F : ℝ → ℝ := fun t => inducedDistance g o (f t)
  have hF : Continuous F := (L23Aux.continuous_distFrom g hg o).comp hf.continuous
  apply (L23Aux.mem_distBall_iff g o (f T) (by linarith : 0 < r + 1)).2
  by_contra hn
  obtain ⟨t, ht, hFt, hbefore⟩ := continuous_first_crossing_Icc hT.1 hF
    (show F 0 < r + 1 by dsimp [F]; rw [hf0]; linarith)
    (le_of_not_gt hn)
  have hlocal : ∀ u ∈ Set.Icc (0 : ℝ) t,
      HermLE (gMat g (f u)) ((c : ℂ) • gMat k (f u)) := by
    intro u hu
    apply hcmp
    apply (L23Aux.mem_distBall_iff g o (f u) (by linarith : 0 < r + 2)).2
    have hh := hbefore u hu
    change inducedDistance g o (f u) ≤ r + 1 at hh
    linarith
  have ht1 : t ≤ 1 := ht.2.trans hT.2
  have hd := distance_le_fieldPathLength g hg f ht.1
    (hf.contMDiffOn.mono (Set.Icc_subset_Icc le_rfl ht1))
  have hcomp := fieldPathLength_le g k f 0 t c hc.le hlocal
  have hsub := fieldPathLength_mono k f (a := 0) (b := t) (A := 0) (B := 1) le_rfl ht1
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

theorem local_ball_comparison (g k l : HermitianField M)
    (hg : MetricSmooth g) (hk : MetricSmooth k) (hl : MetricSmooth l)
    (o p : M.Carrier) {r e c d : ℝ}
    (hr : 0 < r) (he : 0 < e) (hc : 0 < c) (hd : 0 < d)
    (hsmall : Real.sqrt c * e < 1) (hp : p ∈ distBall g o r)
    (hcmp : ∀ x ∈ distBall g o (r + 2),
      HermLE (gMat g x) ((c : ℂ) • gMat k x))
    (hkl : ∀ x ∈ distBall g o (r + 2),
      HermLE (gMat l x) ((d : ℂ) • gMat k x)) :
    distBall k p e ⊆ distBall l p (Real.sqrt d * e) := by
  intro x hx
  obtain ⟨f, hf0, hf1, hf, hlen⟩ := exists_short_smooth_path k hk p x
    ((L23Aux.mem_distBall_iff k p x he).1 hx)
  have hstay := short_path_stays_central g k hg o p hr hc hsmall hp hcmp f hf0 hf hlen
  have hlocal : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      HermLE (gMat l (f t)) ((d : ℂ) • gMat k (f t)) := by
    intro t ht
    apply hkl
    have hh := (L23Aux.mem_distBall_iff g o (f t) (by linarith : 0 < r + 1)).1 (hstay t ht)
    apply (L23Aux.mem_distBall_iff g o (f t) (by linarith : 0 < r + 2)).2
    linarith
  have hdist := distance_le_fieldPathLength l hl f zero_le_one hf.contMDiffOn
  have hcomp := fieldPathLength_le l k f 0 1 d hd.le hlocal
  have hsqrt : 0 < Real.sqrt d := Real.sqrt_pos.2 hd
  have hmul := ENNReal.mul_lt_mul_right
    (ENNReal.ofReal_pos.2 hsqrt).ne' ENNReal.ofReal_ne_top hlen
  have hh := hdist.trans hcomp |>.trans_lt hmul
  rw [hf0, hf1, ← ENNReal.ofReal_mul hsqrt.le] at hh
  exact hh

end Yau.Proofs.C04RescaledTubeAux
