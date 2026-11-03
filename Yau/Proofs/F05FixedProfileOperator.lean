import Yau.Proofs.F05SmoothLaplacian
import Yau.Proofs.F05RestartDatum

/-! The original nonlinear operator on a genuine global smooth profile is
smooth for the supplied metric family. Completeness of the moving metric
is not used. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

def F05ProfileNonlinearJet (h : ℝ → HermitianField M) (τ : ℝ) (g : M.Carrier → ℝ) :
    M.Carrier → ℝ := fun x => Real.exp (-g x)*laplacian (h τ) g x+
      (1-Real.exp (-g x))*scalarCurvature (h τ) x

theorem F05_fixed_profile_laplacian_smooth (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I) {g : M.Carrier → ℝ} (hg : SmoothFn g) :
    SmoothSpaceTime (fun x t => laplacian (h t) g x) I := by
  intro x
  let Q := chartTarget x ×ˢ I
  have hG : ContDiffOn ℝ ∞ (fun q : Point n => g (chartInv x q.1)) Q :=
    (hg x).comp contDiffOn_fst (fun q hq => hq.1)
  have hJets := F05_joint_spatial_jets_smooth (isOpen_extChartAt_target (I := ComplexModel n) x) hG
  have hA := (Yau.F04Proof.flowChartPrincipal_smooth h hh x).1
  have hExpr : ContDiffOn ℝ ∞ (fun q : Point n => ∑ i,∑ j,
      Yau.F04Proof.flowChartPrincipal h x q i j*
        spatialDD (fun p : Point n => g (chartInv x p.1)) q (realVec i) (realVec j)) Q := by
    exact ContDiffOn.sum (fun i _ => ContDiffOn.sum (fun j _ =>
      (F05_contDiffOn_matrix_entry hA i j).mul
        ((hJets.2.clm_apply contDiffOn_const).clm_apply contDiffOn_const)))
  exact hExpr.congr (fun q hq => Yau.F04Proof.flowChartPrincipal_operator h x hg q.1 hq.1 q.2)

theorem F05_fixed_profile_nonlinear_smooth (h : ℝ → HermitianField M) {I : Set ℝ}
    (hh : MetricFamilySmooth h I)
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) I)
    {g : M.Carrier → ℝ} (hg : SmoothFn g) {τ : ℝ} (hτ : τ ∈ I) :
    SmoothFn (F05ProfileNonlinearJet h τ g) := by
  have hLap : SmoothSpaceTime (fun x t => laplacian (h t) g x) I :=
    F05_fixed_profile_laplacian_smooth (M := M) (I := I) (g := g) h hh hg
  intro x
  change ContDiffOn ℝ ∞ (fun z : ComplexVector n =>
    Real.exp (-g (chartInv x z))*laplacian (h τ) g (chartInv x z)+
      (1-Real.exp (-g (chartInv x z)))*scalarCurvature (h τ) (chartInv x z)) (chartTarget x)
  have hEmb : ContDiffOn ℝ ∞ (fun z : ComplexVector n => (z,τ)) (chartTarget x) :=
    contDiffOn_id.prodMk contDiffOn_const
  have hMap : MapsTo (fun z : ComplexVector n => (z,τ)) (chartTarget x) (chartTarget x ×ˢ I) :=
    fun _ hz => ⟨hz,hτ⟩
  have hL0 := (hLap x).comp hEmb hMap
  have hL : ContDiffOn ℝ ∞ (fun z => laplacian (h τ) g (chartInv x z)) (chartTarget x) :=
    hL0
  have hRs0 := (hR x).comp hEmb hMap
  have hRs : ContDiffOn ℝ ∞ (fun z => scalarCurvature (h τ) (chartInv x z)) (chartTarget x) :=
    hRs0
  have hExp : ContDiffOn ℝ ∞ (fun z : ComplexVector n => Real.exp (-g (chartInv x z)))
      (chartTarget x) := (hg x).neg.exp
  exact (hExp.mul hL).add ((contDiffOn_const.sub hExp).mul hRs)

theorem F05_restart_nonlinear_compatible (h : ℝ → HermitianField M) {τ S : ℝ}
    (hS : 0 < S) (p : M.Carrier → ℝ → ℝ) (g : M.Carrier → ℝ)
    (hp : SmoothSpaceTime p (Icc τ (τ+S))) :
    ∀ x, derivWithin (F05RestartDatum τ S p g (F05ProfileNonlinearJet h τ g) x) (Icc 0 S) 0 =
      Real.exp (-F05RestartDatum τ S p g (F05ProfileNonlinearJet h τ g) x 0)*
        laplacian (h τ) (fun y => F05RestartDatum τ S p g (F05ProfileNonlinearJet h τ g) y 0) x+
        (1-Real.exp (-F05RestartDatum τ S p g (F05ProfileNonlinearJet h τ g) x 0))*scalarCurvature (h τ) x := by
  intro x
  rw [F05_restart_time_jet hS p g (F05ProfileNonlinearJet h τ g)
    ((F05_smooth_time_slice hp x).differentiableOn (by simp) τ ⟨le_rfl,by linarith⟩)]
  simp only [F05_restart_initial,F05ProfileNonlinearJet]

end Yau.Proofs.F05Aux
