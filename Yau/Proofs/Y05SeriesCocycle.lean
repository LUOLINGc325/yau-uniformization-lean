import Yau.Proofs.Y05JetSeries

noncomputable section

namespace Yau.Proofs.Y05Aux

open Yau Yau.Blueprint.Alignment Filter
open scoped ContDiff Topology

variable {n d : ℕ}

theorem transition_polynomial_precomp_jet
    {T : ℕ → ℕ → ComplexVector n → ComplexVector n}
    {P : ℕ → ComplexVector n → ℂ} {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ}
    (hTa : ∀ k l, k ≤ l → AnalyticAt ℂ (T k l) 0)
    (hT0 : ∀ k l, k ≤ l → T k l 0 = 0) (hPa : ∀ k, AnalyticAt ℂ (P k) 0)
    (hcocycle : ∀ k j l, k ≤ j → j ≤ l → (T j l ∘ T k j) =ᶠ[𝓝 0] T k l)
    (hBjet : ∀ k l, k ≤ l → ScalarJetEq (scalarEval (B k l)) (fun z => P l (T k l z)) d)
    (k l : ℕ) (hkl : k + 1 ≤ l) :
    ScalarJetEq (scalarEval (B k l)) (fun z => scalarEval (B (k + 1) l) (T k (k + 1) z)) d := by
  have hinner := hTa k (k + 1) (Nat.le_succ k)
  have hout : AnalyticAt ℂ (P l ∘ T (k + 1) l) 0 := by
    have hp : AnalyticAt ℂ (P l) (T (k + 1) l 0) := by
      simpa only [hT0 (k + 1) l hkl] using hPa l
    exact hp.comp (hTa (k + 1) l hkl)
  have hpre := iteratedFDeriv_comp_congr_through hinner.contDiffAt hinner.contDiffAt
    ((Yau.Proofs.Y01Aux.polyEval_contDiff (B (k + 1) l)).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt hout.contDiffAt
    (hT0 k (k + 1) (Nat.le_succ k)) (hT0 k (k + 1) (Nat.le_succ k))
    (fun _ _ => rfl) (hBjet (k + 1) l hkl)
  have heq : ((P l ∘ T (k + 1) l) ∘ T k (k + 1)) =ᶠ[𝓝 0] (P l ∘ T k l) := by
    filter_upwards [hcocycle k (k + 1) l (Nat.le_succ k) hkl] with z hz
    exact congrArg (P l) hz
  intro m hm
  exact (hBjet k l (by omega) m hm).trans
    (((heq.iteratedFDeriv ℂ m).eq_of_nhds).symm.trans (hpre m hm).symm)

theorem transition_polynomial_self_jet
    {T : ℕ → ℕ → ComplexVector n → ComplexVector n}
    {P : ℕ → ComplexVector n → ℂ} {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ}
    (hself : ∀ k, T k k =ᶠ[𝓝 0] id)
    (hBjet : ∀ k l, k ≤ l → ScalarJetEq (scalarEval (B k l)) (fun z => P l (T k l z)) d)
    (k : ℕ) : ScalarJetEq (scalarEval (B k k)) (P k) d := by
  have heq : (fun z => P k (T k k z)) =ᶠ[𝓝 0] P k := by
    filter_upwards [hself k] with z hz
    exact congrArg (P k) hz
  intro m hm
  exact (hBjet k k le_rfl m hm).trans (heq.iteratedFDeriv ℂ m).eq_of_nhds

set_option maxHeartbeats 800000 in
/-- The coefficientwise tail is coherent after composition with the actual
transition germ. Only finite linear operations are exchanged with the sum. -/
theorem coefficient_tail_scalar_cocycle
    {T : ℕ → ℕ → ComplexVector n → ComplexVector n}
    {P : ℕ → ComplexVector n → ℂ}
    {B : ℕ → ℕ → MvPolynomial (Fin n) ℂ} {ell : ℕ → MvPolynomial (Fin n) ℂ}
    (hTa : ∀ k l, k ≤ l → AnalyticAt ℂ (T k l) 0)
    (hT0 : ∀ k l, k ≤ l → T k l 0 = 0) (hPa : ∀ k, AnalyticAt ℂ (P k) 0)
    (hcocycle : ∀ k j l, k ≤ j → j ≤ l → (T j l ∘ T k j) =ᶠ[𝓝 0] T k l)
    (hself : ∀ k, T k k =ᶠ[𝓝 0] id)
    (hBjet : ∀ k l, k ≤ l → ScalarJetEq (scalarEval (B k l)) (fun z => P l (T k l z)) d)
    (hBdeg : ∀ k l, k ≤ l → (B k l).totalDegree ≤ d)
    (hEllDeg : ∀ k, (ell k).totalDegree ≤ d)
    (hSum : ∀ k a, HasSum (fun r : ℕ => (B k (k + r)).coeff a) ((ell k).coeff a)) :
    ∀ k, ScalarJetEq (scalarEval (ell k))
      (fun z => P k z + scalarEval (ell (k + 1)) (T k (k + 1) z)) d := by
  intro k m hm
  have hDirect : HasSum (fun r : ℕ => iteratedFDeriv ℂ m (scalarEval (B k (k + r))) 0)
      (iteratedFDeriv ℂ m (scalarEval (ell k)) 0) := by
    exact hasSum_polynomial_precomp_jets (n := n) (d := d) (F := id) (m := m)
      (fun r => hBdeg k (k + r) (Nat.le_add_right k r)) (hEllDeg k) (hSum k)
      (contDiffAt_id : ContDiffAt ℂ m (id : ComplexVector n → ComplexVector n) 0)
  have hTail : HasSum (fun r : ℕ => iteratedFDeriv ℂ m
      (fun z => scalarEval (B (k + 1) ((k + 1) + r)) (T k (k + 1) z)) 0)
      (iteratedFDeriv ℂ m (fun z => scalarEval (ell (k + 1)) (T k (k + 1) z)) 0) :=
    hasSum_polynomial_precomp_jets (n := n) (d := d) (F := T k (k + 1)) (m := m)
    (fun r => hBdeg (k + 1) ((k + 1) + r) (Nat.le_add_right (k + 1) r))
    (hEllDeg (k + 1)) (hSum (k + 1))
    ((hTa k (k + 1) (Nat.le_succ k)).contDiffAt (n := (m : ℕ∞ω)))
  have hShift : HasSum
      (fun r : ℕ => iteratedFDeriv ℂ m (scalarEval (B k (k + (r + 1)))) 0)
      (iteratedFDeriv ℂ m (fun z => scalarEval (ell (k + 1)) (T k (k + 1) z)) 0) := by
    convert hTail using 1
    funext r
    have H := transition_polynomial_precomp_jet hTa hT0 hPa hcocycle hBjet
      k ((k + 1) + r) (Nat.le_add_right (k + 1) r) m hm
    simpa only [show k + (r + 1) = (k + 1) + r by omega] using H
  have hFull : HasSum
      (fun r : ℕ => iteratedFDeriv ℂ m (scalarEval (B k (k + r))) 0)
      (iteratedFDeriv ℂ m (scalarEval (B k (k + 0))) 0 +
        iteratedFDeriv ℂ m (fun z => scalarEval (ell (k + 1)) (T k (k + 1) z)) 0) :=
    HasSum.zero_add (f := fun r : ℕ => iteratedFDeriv ℂ m (scalarEval (B k (k + r))) 0) hShift
  have hEq := hDirect.unique hFull
  have hselfJet := transition_polynomial_self_jet hself hBjet k m hm
  have hRight : ContDiffAt ℂ m
      (fun z => scalarEval (ell (k + 1)) (T k (k + 1) z)) 0 :=
    ((Yau.Proofs.Y01Aux.polyEval_contDiff (ell (k + 1))).of_le
      (WithTop.coe_le_coe.mpr le_top)).contDiffAt.comp 0
      (hTa k (k + 1) (Nat.le_succ k)).contDiffAt
  calc
    iteratedFDeriv ℂ m (scalarEval (ell k)) 0 =
        iteratedFDeriv ℂ m (scalarEval (B k k)) 0 +
          iteratedFDeriv ℂ m (fun z => scalarEval (ell (k + 1)) (T k (k + 1) z)) 0 := by
      simpa only [Nat.add_zero] using hEq
    _ = iteratedFDeriv ℂ m (P k) 0 +
        iteratedFDeriv ℂ m (fun z => scalarEval (ell (k + 1)) (T k (k + 1) z)) 0 := by rw [hselfJet]
    _ = _ := (iteratedFDeriv_add_apply (hPa k).contDiffAt hRight).symm

end Yau.Proofs.Y05Aux
