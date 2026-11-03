import Yau.LeafProofs.L16WeakWordState

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 4000000
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

theorem weakSpatialWordState_step {n : ℕ} {W V : Set (Point n)}
    (hW : IsOpen W) (hV : IsOpen V) (hVC : IsCompact (closure V)) (hVW : closure V ⊆ W)
    {a : Point n → Mat n} {c : Point n → Yau.RIdx n → ℝ} {lam upper C : ℝ}
    (hC : 0 ≤ C) (hEll : Elliptic W a lam upper)
    (ha : ContDiff ℝ ∞ a) (hca : HasCompactSupport a)
    (hc : ∀ j, ContDiff ℝ ∞ (fun p => c p j))
    (hcc : ∀ j, HasCompactSupport (fun p => c p j))
    (hAVal : ∀ p, ‖a p‖ ≤ C) (hCVal : ∀ j p, |c p j| ≤ C)
    (hADq : ∀ i h p, ‖spatialDifferenceQuotient a (Yau.realVec i) h p‖ ≤ C)
    (hCDq : ∀ j i h p, |spatialDifferenceQuotient (fun q => c q j) (Yau.realVec i) h p| ≤ C)
    (k : ℕ) (U : List (Yau.RIdx n) → Point n → ℝ)
    (hState : WeakSpatialWordState W a c k U) :
    ∃ U' : List (Yau.RIdx n) → Point n → ℝ,
      (∀ v, v.length ≤ k+1 → U' v = U v) ∧ WeakSpatialWordState V a c (k+1) U' := by
  have haEntry (q j : Yau.RIdx n) : ContDiff ℝ ∞ (fun p => a p q j) :=
    (matrixEntryCLM q j).contDiff.comp ha
  have hcaEntry (q j : Yau.RIdx n) : HasCompactSupport (fun p => a p q j) :=
    hca.comp_left (g := fun A : Mat n => A q j) (by simp)
  have hGain (w : {w : List (Yau.RIdx n) // w.length = k}) (i j : Yau.RIdx n) :
      ∃ Z : Point n → ℝ, MemLp Z 2 (volume.restrict V) ∧
        ∀ φ : Point n → ℝ, Test V φ →
          (∫ p, U (j::w.1) p*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V) =
            -(∫ p, Z p*φ p ∂volume.restrict V) := by
    have hw : w.1.length ≤ k := w.2.le
    have hSF (q : Yau.RIdx n) := weakWordSource_weakH1 hW (fun j p => a p q j)
      (haEntry q) (hcaEntry q) U k hState.1 hState.2.1 w.1 hw
    have hSR := weakWordSource_weakH1 hW (fun j p => c p j) hc hcc U k hState.1 hState.2.1 w.1 hw
    have hPF (q : Yau.RIdx n) : MemLp (fun p => energyFlux a (fun p j => U (j::w.1) p) p q) 2 (volume.restrict W) := by
      apply memLp_finsetSum Finset.univ
      intro j _
      exact ((haEntry q j).continuous.memLp_top_of_hasCompactSupport (hcaEntry q j) _).mul
        (hState.1 (j::w.1) (by simp only [List.length_cons]; omega))
    have hPR : MemLp (fun p => ∑ j, c p j*U (j::w.1) p) 2 (volume.restrict W) :=
      memLp_finsetSum Finset.univ (fun j _ =>
        ((hc j).continuous.memLp_top_of_hasCompactSupport (hcc j) _).mul
          (hState.1 (j::w.1) (by simp only [List.length_cons]; omega)))
    have hP (q : Yau.RIdx n) : MemLp (fun p => weakWordFlux a U w.1 p q) 2 (volume.restrict W) := by
      convert! (hPF q).add (hSF q).1 using 1
    have hR : MemLp (weakWordDrift c U w.1) 2 (volume.restrict W) := by
      convert! hPR.add hSR.1 using 1
    exact local_inhomogeneous_spatial_weak_derivative_gain hW hV hVC hVW hC hEll ha hc
      hAVal hCVal hADq hCDq (hState.1 w.1 (by omega))
      (fun j => hState.1 (j::w.1) (by simp only [List.length_cons]; omega))
      hP hR (hState.2.1 w.1 hw) (hState.2.2 w.1 hw)
      (fun q => (hSF q).1) hSR.1 (fun q z => (hSF q).2.1 z) hSR.2.1
      (fun q => (hSF q).2.2) hSR.2.2 (fun _ _ _ => rfl) (fun _ _ => rfl) i j
  choose Z hZ hZWeak using hGain
  let U' : List (Yau.RIdx n) → Point n → ℝ := extendWeakWordFamily k U Z
  have hOld (v : List (Yau.RIdx n)) (hv : v.length ≤ k+1) : U' v = U v :=
    extendWeakWordFamily_eq_old k U Z v hv
  have hVSub : V ⊆ W := subset_closure.trans hVW
  have hOldState : WeakSpatialWordState V a c k U' :=
    weakSpatialWordState_congr_of_low_eq (weakSpatialWordState_mono hState hVSub) hOld
  have hL2New (v : List (Yau.RIdx n)) (hv : v.length ≤ (k+1)+1) :
      MemLp (U' v) 2 (volume.restrict V) := by
    by_cases hLow : v.length ≤ k+1
    · exact hOldState.1 v hLow
    · cases v with
      | nil => simp only [List.length_nil] at hLow; omega
      | cons i v =>
        cases v with
        | nil => simp only [List.length_cons,List.length_nil] at hLow; omega
        | cons j w =>
          have hw : w.length = k := by simp only [List.length_cons] at hv hLow; omega
          have hNew : U' (i::j::w) = Z ⟨w,hw⟩ i j := extendWeakWordFamily_eq_new k U Z ⟨w,hw⟩ i j
          rw [hNew]
          exact hZ ⟨w,hw⟩ i j
  have hWGNew (v : List (Yau.RIdx n)) (hv : v.length ≤ k+1) :
      WeakGradientOn V (U' v) (fun p i => U' (i::v) p) := by
    by_cases hLow : v.length ≤ k
    · exact hOldState.2.1 v hLow
    · cases v with
      | nil => simp only [List.length_nil] at hLow; omega
      | cons j w =>
        have hw : w.length = k := by simp only [List.length_cons] at hv hLow; omega
        intro φ hφ i
        have hNew : U' (i::j::w) = Z ⟨w,hw⟩ i j := extendWeakWordFamily_eq_new k U Z ⟨w,hw⟩ i j
        change (∫ p, U' (j::w) p*fderiv ℝ φ p (Yau.realVec i,0) ∂volume.restrict V) =
          -(∫ p, U' (i::j::w) p*φ p ∂volume.restrict V)
        rw [hOld (j::w) hv,hNew]
        exact hZWeak ⟨w,hw⟩ i j φ hφ
  have hEqNew (v : List (Yau.RIdx n)) (hv : v.length ≤ k+1) :
      WeakDivergenceEvolutionOn V (U' v) (weakWordFlux a U' v) (weakWordDrift c U' v) := by
    by_cases hLow : v.length ≤ k
    · exact hOldState.2.2 v hLow
    · cases v with
      | nil => simp only [List.length_nil] at hLow; omega
      | cons i w =>
        have hw : w.length ≤ k := by simp only [List.length_cons] at hv; omega
        exact weakWordEquation_spatial_derivative hV a c haEntry hcaEntry hc hcc U' k hL2New hWGNew
          w hw (hOldState.2.2 w hw) i
  exact ⟨U',hOld,hL2New,hWGNew,hEqNew⟩

end Yau.LeafProofs.L16Aux
