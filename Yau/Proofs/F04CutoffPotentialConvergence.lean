import Yau.Proofs.F04CutoffLimitRegularity
import Yau.Proofs.F04RhoDominatedMonotoneLimit
import Yau.Proofs.F04DominatedInitialRegularity
import Yau.Proofs.F04CaloricUniqueness
import Yau.Proofs.F04SmoothSubcaloric

open MeasureTheory Filter Set
open scoped Topology ContDiff Manifold
noncomputable section
namespace Yau.F04Proof
open Yau.Blueprint

/-- The actual cutoff-potential limit is the SAME supplied rho. The full
 source equation and closed-face smoothness are first genuinely proved;
 only then is registered dominated caloric uniqueness applied. No new
 evolving heat kernel or unexplained full-source solver is introduced. -/
theorem cutoff_potentials_tend_rho_from_dependencies
    (hP07 : P07) (hF03 : F03) (hG02 : G02)
    {n : ℕ} (hn : 0 < n) (X : KahlerManifold n) (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) {S T : ℝ} (hS : 0 < S) (hT : 0 < T) (hTS : T < S)
    (qs : ℕ → Pt X → ℝ)
    (hCut : ∀ K : Set (Pt X), IsCompact K → ∃ J : ℕ, ∀ j ≥ J, ∀ x ∈ K, qs j x = 1)
    (v : ℕ → STF X)
    (hMono : ∀ x t, t ∈ Icc 0 S → Monotone (fun j => v j x t))
    (hBound : ∀ j x t, t ∈ Icc 0 S → 0 ≤ v j x t ∧ v j x t ≤ ρ x t)
    (h0 : ∀ j x, v j x 0 = 0) (hv : ∀ j, SmoothSpaceTime (v j) (Ioo 0 S))
    (hPDE : ∀ j x t, t ∈ Ioo 0 S → heatOp h (Icc 0 S) (v j) x t = qs j x * source X h x t) :
    ∀ x t, t ∈ Icc 0 T → Tendsto (fun j => v j x t) atTop (𝓝 (ρ x t)) := by
  obtain ⟨z,hTend,hzBound,_hLe,hz0⟩ := rho_dominated_monotone_limit hS ρ v hMono hBound h0
  obtain ⟨hzPos,hzPDE⟩ := flow_cutoff_potential_limit_positive_regularization hn X o h U P ρ hloc
    hS qs hCut v z hv hPDE (fun j x t ht => hBound j x t (Ioo_subset_Icc_self ht))
    (fun x t ht => hTend x t (Ioo_subset_Icc_self ht))
  have hOne : SmoothFn (fun _ : Pt X => (1 : ℝ)) := fun _ => contDiffOn_const
  have hzPDEone : ∀ x t, t ∈ Ioo 0 S → heatOp h (Icc 0 S) z x t = (1 : ℝ)*source X h x t := by
    simpa only [one_mul] using hzPDE
  obtain ⟨hz,hzClosedEq⟩ := flow_dominated_initial_regularization hn X o h U P ρ hloc hS hT hTS
    (fun _ => 1) hOne z hzPos hz0 (fun x t ht => hzBound x t (Ioo_subset_Icc_self ht)) hzPDEone
  have hρ : SmoothSpaceTime ρ (Icc 0 T) := fun c => (hloc.2.2.2.1 c).mono
    (Set.prod_mono (Subset.refl _) (fun _ ht => ht.1))
  have hDiff : SmoothSpaceTime (fun x t => ρ x t-z x t) (Icc 0 T) := fun c => (hρ c).sub (hz c)
  have hDiffBound : ∀ x t, t ∈ Icc 0 T → 0 ≤ ρ x t-z x t ∧ ρ x t-z x t ≤ ρ x t := by
    intro x t ht
    have hb := hzBound x t ⟨ht.1,ht.2.trans hTS.le⟩
    exact ⟨sub_nonneg.mpr hb.2,sub_le_self _ hb.1⟩
  have hCal : ∀ x t, t ∈ Icc 0 T → heatOp h (Icc 0 T) (fun x t => ρ x t-z x t) x t = 0 := by
    intro x t ht
    rw [heatOp_sub_smooth h hT hρ hz x ht,rho_source_equation o h U P ρ hloc T hT x t ht,
      hzClosedEq x t ht,one_mul,sub_self]
  have hZero := dominated_caloric_uniqueness_from_dependencies hP07 hF03 hG02 X o h U P ρ hloc
    hT hDiff hDiffBound hCal
  intro x t ht
  have he : z x t = ρ x t := by linarith only [hZero x t ht]
  rw [← he]
  exact hTend x t ⟨ht.1,ht.2.trans hTS.le⟩

end Yau.F04Proof
