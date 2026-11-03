import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.UniformSpace.HeineCantor

/-! Local operations on the full compact spatial initial jets. -/
noncomputable section
open Filter Set
open scoped Topology ContDiff
namespace Yau.NodeProofs.P06Aux.PDETypeTrace
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- All derivative orders, including zero, uniformly on each fixed compact. -/
def SmallJetsOn (O : Set E) (f : ℝ → E → F) : Prop :=
  ∀ K : Set E, IsCompact K → K ⊆ O → ∀ j : ℕ, ∀ ε : ℝ, 0 < ε →
    ∀ᶠ t in 𝓝[>] (0 : ℝ), ∀ z ∈ K, ‖iteratedFDeriv ℝ j (f t) z‖ < ε

theorem smallJetsOn_zero (O : Set E) : SmallJetsOn O (fun _ _ => (0 : F)) := by
  intro K hK hKO j ε hε
  exact Eventually.of_forall (fun t z hz => by simpa using hε)

theorem smallJetsOn_add {O : Set E} (hO : IsOpen O) {f g : ℝ → E → F}
    (hf : ∀ t, 0 < t → ContDiffOn ℝ ∞ (f t) O)
    (hg : ∀ t, 0 < t → ContDiffOn ℝ ∞ (g t) O)
    (hfi : SmallJetsOn O f) (hgi : SmallJetsOn O g) :
    SmallJetsOn O (fun t z => f t z + g t z) := by
  intro K hK hKO j ε hε
  filter_upwards [hfi K hK hKO j (ε / 2) (by positivity),
    hgi K hK hKO j (ε / 2) (by positivity), self_mem_nhdsWithin] with t hft hgt ht
  intro z hz
  have hfj := ((hf t ht).contDiffAt (hO.mem_nhds (hKO hz))).of_le (by simp : (j : ℕ∞ω) ≤ ∞)
  have hgj := ((hg t ht).contDiffAt (hO.mem_nhds (hKO hz))).of_le (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [fun_iteratedFDeriv_add_apply hfj hgj]
  exact (norm_add_le _ _).trans_lt (by linarith [hft z hz, hgt z hz])

theorem smallJetsOn_const_mul {O : Set E} (hO : IsOpen O) {f : ℝ → E → ℝ}
    (hf : ∀ t, 0 < t → ContDiffOn ℝ ∞ (f t) O)
    (hfi : SmallJetsOn O f) (c : ℝ) :
    SmallJetsOn O (fun t z => c * f t z) := by
  intro K hK hKO j ε hε
  have hd : 0 < ε / (|c| + 1) := by positivity
  filter_upwards [hfi K hK hKO j (ε / (|c| + 1)) hd,
    self_mem_nhdsWithin] with t hft ht
  intro z hz
  have hfj := ((hf t ht).contDiffAt (hO.mem_nhds (hKO hz))).of_le (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [show (fun z => c * f t z) = c • f t by rfl,
    iteratedFDeriv_const_smul_apply hfj, norm_smul, Real.norm_eq_abs]
  have hd' : (|c| + 1) * (ε / (|c| + 1)) = ε := mul_div_cancel₀ _ (by positivity)
  calc
    _ ≤ |c| * (ε / (|c| + 1)) := mul_le_mul_of_nonneg_left (hft z hz).le (abs_nonneg c)
    _ < (|c| + 1) * (ε / (|c| + 1)) := mul_lt_mul_of_pos_right (by linarith) hd
    _ = ε := hd'

theorem smallJetsOn_finset_sum {ι : Type*} {O : Set E} (hO : IsOpen O)
    (s : Finset ι) (f : ι → ℝ → E → F)
    (hf : ∀ i ∈ s, ∀ t, 0 < t → ContDiffOn ℝ ∞ (f i t) O)
    (hfi : ∀ i ∈ s, SmallJetsOn O (f i)) :
    SmallJetsOn O (fun t z => ∑ i ∈ s, f i t z) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using smallJetsOn_zero (F := F) O
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact smallJetsOn_add hO (hf i (Finset.mem_insert_self _ _))
      (fun t ht => ContDiffOn.sum (fun a ha => hf a (Finset.mem_insert_of_mem ha) t ht))
      (hfi i (Finset.mem_insert_self _ _))
      (ih (fun a ha => hf a (Finset.mem_insert_of_mem ha))
        (fun a ha => hfi a (Finset.mem_insert_of_mem ha)))

theorem smallJetsOn_mul {O : Set E} (hO : IsOpen O) {f : ℝ → E → ℝ}
    (hf : ∀ t, 0 < t → ContDiffOn ℝ ∞ (f t) O)
    (hfi : SmallJetsOn O f) {a : E → ℝ} (ha : ContDiffOn ℝ ∞ a O) :
    SmallJetsOn O (fun t z => a z * f t z) := by
  intro K hK hKO j ε hε
  let C : E → ℝ := fun z => ∑ i ∈ Finset.range (j + 1),
    (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i a z‖
  have hC : ContinuousOn C K := by
    apply continuousOn_finsetSum
    intro i hi
    exact continuousOn_const.mul
      (((ContinuousOn.continuousOn_iteratedFDeriv ha hO (by simp)).mono hKO).norm)
  obtain ⟨D, hD⟩ := hK.exists_bound_of_continuousOn hC
  let B : ℝ := max D 0 + 1
  have hB : 0 < B := by dsimp [B]; positivity
  have hδ : 0 < ε / B := div_pos hε hB
  have hsmall : ∀ᶠ t in 𝓝[>] (0 : ℝ),
      ∀ i ∈ Finset.range (j + 1), ∀ z ∈ K,
        ‖iteratedFDeriv ℝ (j - i) (f t) z‖ < ε / B := by
    exact (Finset.eventually_all _).mpr (fun i hi => hfi K hK hKO (j - i) (ε / B) hδ)
  filter_upwards [hsmall, self_mem_nhdsWithin] with t ht htp
  intro z hz
  have hza : ContDiffAt ℝ ∞ a z := ha.contDiffAt (hO.mem_nhds (hKO hz))
  have hzf : ContDiffAt ℝ ∞ (f t) z := (hf t htp).contDiffAt (hO.mem_nhds (hKO hz))
  have hwithin := norm_iteratedFDerivWithin_mul_le ha (hf t htp)
    hO.uniqueDiffOn (hKO hz) (by simp : (j : ℕ∞ω) ≤ ∞)
  rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
    ((hza.mul hzf).of_le (by simp)) (hKO hz)] at hwithin
  simp_rw [iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
    (hza.of_le (by simp)) (hKO hz),
    iteratedFDerivWithin_eq_iteratedFDeriv hO.uniqueDiffOn
      (hzf.of_le (by simp)) (hKO hz)] at hwithin
  have hCnon : 0 ≤ C z := Finset.sum_nonneg (fun i hi => mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _))
  have hCbound : C z < B := by
    have hh := hD z hz
    rw [Real.norm_eq_abs, abs_of_nonneg hCnon] at hh
    exact lt_of_le_of_lt hh (by dsimp [B]; linarith [le_max_left D 0])
  calc
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i a z‖ *
          ‖iteratedFDeriv ℝ (j - i) (f t) z‖ := hwithin
    _ ≤ ∑ i ∈ Finset.range (j + 1),
        (j.choose i : ℝ) * ‖iteratedFDeriv ℝ i a z‖ * (ε / B) := by
      exact Finset.sum_le_sum (fun i hi => mul_le_mul_of_nonneg_left (ht i hi z hz).le
        (mul_nonneg (Nat.cast_nonneg _) (norm_nonneg _)))
    _ = C z * (ε / B) := (Finset.sum_mul ..).symm
    _ < B * (ε / B) := mul_lt_mul_of_pos_right hCbound hδ
    _ = ε := mul_div_cancel₀ _ hB.ne'

end Yau.NodeProofs.P06Aux.PDETypeTrace
