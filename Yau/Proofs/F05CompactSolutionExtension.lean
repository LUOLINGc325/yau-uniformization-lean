import Yau.Proofs.F05CompactDirichletSolution
import Yau.Proofs.F05SmoothRestartLocal
import Yau.Proofs.F05ShiftedRestart
import Yau.Proofs.F05ManifoldPasteContinuity

/-! Every actual compact-domain solution strictly before the supplied
horizon extends. The smooth terminal profile, compatible restart datum,
local solver and joining time jet are all obtained from proved theorems. -/

open Set
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_compact_solution_extend (hn : 0 < n) {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) {χ : Fin A.count → M.Carrier → ℝ} (hχ : F05Partition O A χ)
    (h : ℝ → HermitianField M) (p w : M.Carrier → ℝ → ℝ) {τ S : ℝ}
    (hτ : 0 < τ) (hτS : τ < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hp : SmoothSpaceTime p (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (hw : F05CompactDirichletSolution O A h p τ w) :
    ∃ (T : ℝ) (v : M.Carrier → ℝ → ℝ), τ < T ∧ T ≤ S ∧
      F05CompactDirichletSolution O A h p T v ∧
      ∀ x ∈ closure O, ∀ t ∈ Icc 0 τ, v x t = w x t := by
  have hSub : Icc (0 : ℝ) τ ⊆ Icc 0 S := Icc_subset_Icc le_rfl hτS.le
  have hhτ : MetricFamilySmooth h (Icc 0 τ) :=
    fun x a b => (hh x a b).mono (prod_mono subset_rfl hSub)
  have hpτ : SmoothSpaceTime p (Icc 0 τ) :=
    fun x => (hp x).mono (prod_mono subset_rfl hSub)
  have hRτ : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 τ) :=
    fun x => (hR x).mono (prod_mono subset_rfl hSub)
  have hSmooth := F05_compact_solution_positive_smooth hn hA h p w hτ hhτ hpτ hRτ hw
  obtain ⟨β,C,hβ,hβ1,hC,hSch,hCont,h0,hBoundary,hEq⟩ := hw
  obtain ⟨ε,D,hε,hεS,hε1,hD,hSolve⟩ := F05_smooth_local_restart hn hA hχ h hτ hτS
    hh hR p w hp hβ hβ1 (fun i => (hSch i).1) hBoundary
    (fun x hx => hEq x hx τ ⟨hτ.le,le_rfl⟩) hSmooth
  obtain ⟨v,hVSch,hVCont,hV0,hVBoundary,hVEq,hVSmooth⟩ := hSolve ε hε le_rfl
  let vShift := F05ShiftedRestart τ v
  have hShiftSch := F05_shifted_restart_schauder (τ := τ) A hε v hVSch
  have hShiftEq := F05_shifted_restart_equation (τ := τ) hA h hε v (fun i => (hVSch i).1) hVEq
  have hTrace (x : M.Carrier) (hx : x ∈ closure O) : w x τ = vShift x τ := by
    simpa only [vShift,F05ShiftedRestart,sub_self] using (hV0 x hx).symm
  have hEnd : τ < τ+ε := by linarith
  have hPaste := F05_manifold_nonlinear_paste hA h hτ hEnd hβ w vShift
    hSch hShiftSch hTrace hEq hShiftEq
  let W := F05ManifoldTimePaste τ w vShift
  have hWCont := F05_manifold_timePaste_continuous hτ.le hEnd.le w vShift hCont
    (F05_shifted_restart_continuous (τ := τ) v hVCont) hTrace
  have hWSol : F05CompactDirichletSolution O A h p (τ+ε) W := by
    refine ⟨β,2*(C+4*D),hβ,hβ1,by positivity,hPaste.1,hWCont,?_,?_,hPaste.2⟩
    · intro x hx
      simpa only [W,F05ManifoldTimePaste,hτ.le,ite_true] using h0 x hx
    · intro x hx t ht
      by_cases htτ : t ≤ τ
      · simpa only [W,F05ManifoldTimePaste,htτ,ite_true] using hBoundary x hx t ⟨ht.1,htτ⟩
      · have htε : t-τ ∈ Icc 0 ε := by constructor <;> linarith [ht.2]
        have hValue := hVBoundary x hx (t-τ) htε
        simpa only [W,F05ManifoldTimePaste,htτ,ite_false,vShift,F05ShiftedRestart,
          sub_add_cancel] using hValue
  refine ⟨τ+ε,W,hEnd,by linarith,hWSol,?_⟩
  intro x hx t ht
  simp only [W,F05ManifoldTimePaste,ht.2,ite_true]

end Yau.Proofs.F05Aux
