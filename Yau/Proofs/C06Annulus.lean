import Yau.Proofs.C06LogSupport
import Yau.Proofs.C06PshTests
import Yau.Proofs.C06AffineLevi

noncomputable section
open Filter Set
open scoped Topology ContDiff Manifold

namespace Yau.Proofs.C06Aux

open Yau Yau.Blueprint Yau.LeafProofs L12Aux

variable {n : ℕ}

/-- The actual logarithmic upper support proves annular comparison for every
positive slope. The outer sphere is chosen using only the global real bound. -/
theorem logarithmic_barrier_comparison (X : KahlerManifold n)
    {v : Pt X → ℝ} (hv : IsPsh (fun x => (v x : EReal)))
    {B : ℝ} (hB : ∀ x, v x ≤ B) (o : Pt X)
    {r a ε : ℝ} (hr : 0 < r) (hε : 0 < ε)
    (hlocal : ∀ x, inducedDistance X.metric.form o x ≤ r → v x ≤ a)
    (y : Pt X) (hy : r ≤ inducedDistance X.metric.form o y) :
    v y ≤ a + ε * (Real.log (inducedDistance X.metric.form o y ^ 2) - Real.log (r ^ 2)) := by
  let d : Pt X → ℝ := inducedDistance X.metric.form o
  have hd : Continuous d := continuous_distFrom X.metric o
  let G : ℝ → ℝ := fun R => a + ε * (Real.log (R ^ 2) - Real.log (r ^ 2))
  have hG : Tendsto G atTop atTop := by
    have hlog : Tendsto (fun R : ℝ => Real.log (R ^ 2)) atTop atTop :=
      Real.tendsto_log_atTop.comp (tendsto_pow_atTop (by norm_num : 2 ≠ 0))
    exact tendsto_atTop_add_const_left atTop a
      ((tendsto_atTop_add_const_right atTop (-Real.log (r ^ 2)) hlog).const_mul_atTop hε)
  have hlarge : ∀ᶠ R : ℝ in atTop, B < G R ∧ d y < R ∧ r < R := by
    filter_upwards [hG.eventually_gt_atTop B, eventually_gt_atTop (d y),
      eventually_gt_atTop r] with R hRG hRy hRr
    exact ⟨hRG, hRy, hRr⟩
  obtain ⟨R, hRG, hRy, hRr⟩ := hlarge.exists
  let K : Set (Pt X) := {x | r ≤ d x} ∩ {x | d x ≤ R}
  have hK : IsCompact K :=
    (isCompact_inducedDistance_sublevel X.metric o R).inter_left
      (isClosed_le continuous_const hd)
  have hyK : y ∈ K := ⟨hy, hRy.le⟩
  have hlogK : ContinuousOn (fun x => Real.log (d x ^ 2)) K :=
    (hd.pow 2).continuousOn.log (fun x hx =>
      pow_ne_zero 2 (ne_of_gt (hr.trans_le hx.1)))
  let F : Pt X → ℝ := fun x => v x - ε * Real.log (d x ^ 2)
  have hF : UpperSemicontinuousOn F K := by
    exact ((upperSemicontinuous_of_coe hv.2.1).upperSemicontinuousOn K).add
      ((continuousOn_const.mul hlogK).neg.upperSemicontinuousOn)
  by_contra hbad
  have hyLarge : a - ε * Real.log (r ^ 2) < F y := by
    dsimp only [F, d]
    linarith [lt_of_not_ge hbad]
  obtain ⟨q, hq, hmax⟩ := hF.exists_isMaxOn ⟨y, hyK⟩ hK
  have hqLarge : a - ε * Real.log (r ^ 2) < F q := hyLarge.trans_le (hmax hyK)
  have hqr : r < d q := by
    by_contra hn
    have hle : d q ≤ r := le_of_not_gt hn
    have heq : d q = r := le_antisymm hle hq.1
    have hvq := hlocal q hle
    dsimp only [F] at hqLarge
    rw [heq] at hqLarge
    linarith
  have hqR : d q < R := by
    by_contra hn
    have heq : d q = R := le_antisymm hq.2 (le_of_not_gt hn)
    have hvq := hB q
    dsimp only [F] at hqLarge
    dsimp only [G] at hRG
    rw [heq] at hqLarge
    linarith
  have hKnhds : K ∈ 𝓝 q := by
    have H := hd.continuousAt.preimage_mem_nhds (isOpen_Ioo.mem_nhds ⟨hqr, hqR⟩)
    exact mem_of_superset H (fun x hx => ⟨hx.1.le, hx.2.le⟩)
  have hmaxLocal : ∀ᶠ x in 𝓝 q, F x ≤ F q :=
    mem_of_superset hKnhds (fun x hx => hmax hx)
  have hneq : o ≠ q := by
    intro heq
    have H : d q = 0 := X.metric.induced_distance_eq_zero.mpr heq
    linarith
  obtain ⟨S, hS, hSval, hSupper, w, hSneg⟩ := logDistanceSquare_strictUpperSupport X o q hneq
  have hi : chartInv q (chartPt q q) = q :=
    (extChartAt (ComplexModel n) q).left_inv (mem_extChartAt_source q)
  have hInv : Tendsto (chartInv q) (𝓝 (chartPt q q)) (𝓝 q) := by
    have H := (continuousAt_extChartAt_symm (I := ComplexModel n) q).tendsto
    change Tendsto (chartInv q) (𝓝 (chartPt q q)) (𝓝 (chartInv q (chartPt q q))) at H
    rwa [hi] at H
  let b : ℝ := v q - ε * S (chartPt q q)
  let φ : ComplexVector n → ℝ := fun z => ε * S z + b
  have hφ : ContDiffAt ℝ 2 φ (chartPt q q) :=
    (contDiffAt_const.mul hS).add contDiffAt_const
  have hcontact : (v (chartInv q (chartPt q q)) : EReal) = (φ (chartPt q q) : EReal) := by
    congr 1
    rw [hi]
    dsimp only [φ, b]
    ring
  have hupper : ∀ᶠ z in 𝓝 (chartPt q q), (v (chartInv q z) : EReal) ≤ (φ z : EReal) := by
    filter_upwards [hInv.eventually hmaxLocal, hSupper] with z hz hzS
    apply EReal.coe_le_coe_iff.mpr
    have H := mul_le_mul_of_nonneg_left hzS hε.le
    dsimp only [F] at hz
    change S (chartPt q q) = Real.log (d q ^ 2) at hSval
    change Real.log (d (chartInv q z) ^ 2) ≤ S z at hzS
    dsimp only [φ, b]
    rw [hSval]
    linarith
  have H := psh_upperTest_levi_nonneg hv q (mem_extChartAt_target q) hφ hcontact hupper w
  change 0 ≤ leviDirection (leviC (fun z => ε * S z + b) (chartPt q q)) w at H
  rw [leviDirection_affine hS ε b w] at H
  exact (not_lt_of_ge H) (mul_neg_of_pos_of_neg hε hSneg)

end Yau.Proofs.C06Aux
