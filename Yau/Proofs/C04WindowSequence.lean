import Yau.Proofs.C04ClockInverse
import Yau.Proofs.C04GoodWindows

/-! Multiplicative good windows for the original physical-time clock. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open MeasureTheory Filter

namespace Yau.Proofs.C04Aux
open Yau Blueprint

variable {n : ℕ}

/-- Every fixed 0<a<1 admits the original S_i windows, with all physical
preimages quantified exactly as in RicciWindows. -/
theorem good_window_sequence (X : KahlerManifold n) (o : Pt X)
    (h : Flow X) (U P ρ : STF X) (hf : LocalizedFlow X o h U P ρ)
    (hH : HarnackCompleteness X o h) {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ S : ℕ → ℝ, ∃ K : ℝ, (∀ i, 0 < S i) ∧ Tendsto S atTop atTop ∧
      ∀ i t t', 0 ≤ t → 0 ≤ t' → ρ o t = 2 * S i → ρ o t' = a * S i →
        clockSpeed o h t ≤ K * clockSpeed o h t' := by
  obtain ⟨A, hA, hsA, time, htime, hleft, hstrict, htinf⟩ :=
    clock_inverse X o h U P ρ hf hH
  let Q := fun s => clockSpeed o h (time s)
  have hQmono : MonotoneOn Q (Set.Ici (ρ o A)) := by
    intro s hs s' hs' hss'
    apply clockSpeed_monotoneOn X o h U P ρ hf hH zero_lt_one
      (hA.trans (htime s hs).1) (hA.trans (htime s' hs').1)
    exact hstrict.monotoneOn hs hs' hss'
  have hQpos : 0 < Q (ρ o A) := by
    exact mul_pos (zero_lt_one.trans_le (hA.trans (htime _ (le_refl _)).1))
      (scalar_pos X o h hH (zero_le_one.trans (hA.trans (htime _ (le_refl _)).1)) o)
  have hQlow : ∀ T, ∃ s, T ≤ s ∧ Q s ≤ 3 * s := by
    intro T
    let target := max T (ρ o A)
    have htarget : ρ o A ≤ target := le_max_right _ _
    obtain ⟨t, ht, hb⟩ := clockSpeed_liminf_bound X o h U P ρ hf hH 1 zero_lt_one
      (time target)
    have hAt : A ≤ t := (htime target htarget).1.trans ht
    have hs : target ≤ ρ o t := by
      rw [← (htime target htarget).2]
      exact (rho_strictMonoOn X o h U P ρ hf hH (zero_lt_one.trans_le hA)).monotoneOn
        (htime target htarget).1 hAt ht
    refine ⟨ρ o t, (le_max_left _ _).trans hs, ?_⟩
    simpa only [Q, hleft t hAt, show (2 : ℝ) + 1 = 3 by norm_num] using hb
  let L := 2 / a
  let K := L ^ 2 + 1
  have hL : 1 < L := (lt_div_iff₀ ha).mpr (by linarith)
  have hK : L ^ 2 < K := by dsimp [K]; linarith
  have hgood := exists_multiplicative_good_window (zero_lt_one.trans_le hsA) hL hK
    hQmono hQpos hQlow
  choose r hr hrA hrq using fun i : ℕ => hgood (i + ρ o A)
  let S := fun i => r i / a
  have hrpos : ∀ i, 0 < r i := fun i => (zero_lt_one.trans_le hsA).trans_le (hrA i)
  have hSr : ∀ i, r i ≤ S i := by
    intro i
    exact (le_div_iff₀ ha).mpr (mul_le_of_le_one_right (hrpos i).le ha1.le)
  have hpre : ∀ s, ρ o A ≤ s → ∀ t, 0 ≤ t → ρ o t = s → t = time s := by
    intro s hs t ht heq
    exact (rho_strictMonoOn_nonneg X o h U P ρ hf hH).injOn ht
      (zero_le_one.trans (hA.trans (htime s hs).1))
      (heq.trans (htime s hs).2.symm)
  refine ⟨S, K, fun i => div_pos (hrpos i) ha, ?_, ?_⟩
  · apply tendsto_atTop_mono (g := S) (f := fun i : ℕ => (i : ℝ))
    · intro i
      have hi : (i : ℝ) ≤ r i := by linarith [hr i]
      exact hi.trans (hSr i)
    · exact tendsto_natCast_atTop_atTop
  · intro i t t' ht ht' hst hst'
    have hsmall : a * S i = r i := by dsimp [S]; field_simp
    have hlarge : 2 * S i = L * r i := by dsimp [S, L]; ring
    have hlargeA : ρ o A ≤ L * r i :=
      (hrA i).trans (le_mul_of_one_le_left (hrpos i).le hL.le)
    have htEq : t = time (L * r i) := hpre _ hlargeA t ht (hst.trans hlarge)
    have htEq' : t' = time (r i) := hpre _ (hrA i) t' ht' (hst'.trans hsmall)
    simpa only [Q, ← htEq, ← htEq'] using hrq i

end Yau.Proofs.C04Aux
