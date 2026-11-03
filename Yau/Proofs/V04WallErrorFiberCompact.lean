import Yau.Proofs.V04WallErrorFiberModel

/-! A radius-independent bound on each member of the original finite
cotangent chart cover. The auxiliary inverse radius ranges over `[0,1]`. -/

open scoped Manifold Topology ContDiff Matrix ComplexOrder
noncomputable section
namespace Yau.Blueprint.V04Proof.WallErrorAux
open Yau Yau.Blueprint V03Proof
variable {n q : ℕ} {X : KahlerManifold n}

theorem exists_fiber_chart_bound {d : VariationData X q} (hd : VariationSetup d)
    (j : ℕ) (x : Pt X) {C : Set (CotangentCoord n)} (hC : IsCompact C)
    (hTarget : C ⊆ cotangentTarget x) :
    ∃ M : ℝ, 1 ≤ M ∧ ∀ z ∈ C, ∀ t ∈ Set.Icc 0 d.T,
      ∀ s ∈ Set.Icc d.cylinderTimeLo d.cylinderTimeHi, ∀ r ∈ Set.Icc (0 : ℝ) 1,
      |clearedFiberPolynomial
        (leviMatrix (fiberNormModel d x t) z cotangentDir)
        (leviMatrix (fiberBaseModel d j x t) z cotangentDir)
        (fiberBaseCleared d j x z) (fiberFiberCleared d x z)
        (deltaBase d j (cotangentChartInv x z).1) (normalizedFiberProfile d x z) r (1 + s)| ≤ M := by
  let K : Set ((CotangentCoord n × ℝ) × (ℝ × ℝ)) :=
    (C ×ˢ Set.Icc 0 d.T) ×ˢ
      (Set.Icc d.cylinderTimeLo d.cylinderTimeHi ×ˢ Set.Icc (0 : ℝ) 1)
  have hK : IsCompact K := (hC.prod isCompact_Icc).prod (isCompact_Icc.prod isCompact_Icc)
  have hz : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) => p.1.1) K :=
    continuous_fst.fst.continuousOn
  have hzt : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) => p.1) K :=
    continuous_fst.continuousOn
  have hzTarget : Set.MapsTo (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) => p.1.1)
      K (cotangentTarget x) := fun p hp => hTarget hp.1.1
  have hztTarget : Set.MapsTo (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) => p.1)
      K (cotangentTarget x ×ˢ Set.Icc 0 d.extendedT) :=
    fun p hp => ⟨hTarget hp.1.1, hp.1.2.1, hp.1.2.2.trans hd.2.1.le⟩
  have hA : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) =>
      leviMatrix (fiberNormModel d x p.1.2) p.1.1 cotangentDir) K := by
    apply continuousOn_pi.2
    intro a
    apply continuousOn_pi.2
    intro b
    exact (fiberNormHessian_entry_contDiffOn hd x a b).continuousOn.comp hzt hztTarget
  have hS : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) =>
      leviMatrix (fiberBaseModel d j x p.1.2) p.1.1 cotangentDir) K := by
    apply continuousOn_pi.2
    intro a
    apply continuousOn_pi.2
    intro b
    exact (fiberBaseHessian_entry_contDiffOn hd j x a b).continuousOn.comp hzt hztTarget
  have hB : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) =>
      fiberBaseCleared d j x p.1.1) K := by
    apply continuousOn_pi.2
    intro a
    apply continuousOn_pi.2
    intro b
    exact (fiberBaseCleared_entry_contDiffOn hd j x a b).continuousOn.comp hz hzTarget
  have hF : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) =>
      fiberFiberCleared d x p.1.1) K := by
    apply continuousOn_pi.2
    intro a
    apply continuousOn_pi.2
    intro b
    exact (fiberFiberCleared_entry_contDiffOn hd x a b).continuousOn.comp hz hzTarget
  have hδ : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) =>
      deltaBase d j (cotangentChartInv x p.1.1).1) K :=
    (deltaBase_chart_contDiffOn hd j x).continuousOn.comp hz hzTarget
  have hε : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) =>
      normalizedFiberProfile d x p.1.1) K :=
    (normalizedFiberProfile_contDiffOn hd x).continuousOn.comp hz hzTarget
  have hr : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) => p.2.2) K :=
    continuous_snd.snd.continuousOn
  have ha : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) => 1 + p.2.1) K :=
    (continuous_const.add continuous_snd.fst).continuousOn
  have hAF := continuous_symplecticCross.comp_continuousOn (hA.prodMk (ha.smul hF))
  have hSF := continuous_symplecticCross.comp_continuousOn (hS.prodMk (ha.smul hF))
  have hBF := continuous_symplecticCross.comp_continuousOn ((ha.smul hB).prodMk (ha.smul hF))
  have hFF := continuous_symplecticP.comp_continuousOn (ha.smul hF)
  have hE : ContinuousOn (fun p : (CotangentCoord n × ℝ) × (ℝ × ℝ) =>
      clearedFiberPolynomial
        (leviMatrix (fiberNormModel d x p.1.2) p.1.1 cotangentDir)
        (leviMatrix (fiberBaseModel d j x p.1.2) p.1.1 cotangentDir)
        (fiberBaseCleared d j x p.1.1) (fiberFiberCleared d x p.1.1)
        (deltaBase d j (cotangentChartInv x p.1.1).1) (normalizedFiberProfile d x p.1.1)
        p.2.2 (1 + p.2.1)) K := by
    exact (((((hδ.pow 6).mul (hε.pow 3)).mul hAF).add
      ((((hr.pow 2).mul (hδ.pow 6)).mul (hε.pow 3)).mul hSF)).add
        ((((hr.pow 2).mul (hδ.pow 3)).mul (hε.pow 3)).mul hBF)).add
          (((hr.pow 2).mul (hδ.pow 6)).mul hFF)
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hE
  refine ⟨max 1 M, le_max_left _ _, ?_⟩
  intro z hz t ht s hs r hr
  apply le_trans ?_ (le_max_right 1 M)
  simpa only [Real.norm_eq_abs] using hM ((z, t), (s, r)) ⟨⟨hz, ht⟩, hs, hr⟩

end Yau.Blueprint.V04Proof.WallErrorAux
