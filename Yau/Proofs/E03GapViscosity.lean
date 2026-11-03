import Yau.Proofs.E03TestCalculus
import Yau.Proofs.E03ScalarAlgebra

/-! The original ellipsoid lower-test inequality gives the original scalar upper-test inequality. -/

noncomputable section
open scoped Manifold Topology ContDiff Matrix ComplexOrder
open Filter Set

namespace Yau.NodeProofs.E03Aux
open Yau Yau.Blueprint
variable {n : ℕ} {X : KahlerManifold n}

theorem scalarGap_nonlinearViscositySub (o : Pt X) (h : Flow X) (U P ρ : STF X)
    (hloc : LocalizedFlow X o h U P ρ) (hopt : OptimizerContacts X h ρ)
    (hcomp : EllipsoidComparison X h) (T : ℝ) (hT : 0 < T)
    (S : ℝ) (hST : S < T) : NonlinearViscositySub h S (scalarGap X h T) := by
  intro x t ht htS φ hφ htouch
  have htT : t < T := htS.trans hST
  have hz : chartPt x x ∈ chartTarget x := mem_extChartAt_target (I := ComplexModel n) x
  have hx : chartInv x (chartPt x x) = x :=
    (extChartAt (ComplexModel n) x).left_inv (mem_extChartAt_source x)
  let testFn : ComplexVector n × ℝ → ℝ := fun p =>
    -logDet (h p.2) x p.1 - φ (chartInv x p.1) p.2
  have hopen : IsOpen (chartTarget x ×ˢ Ioo 0 T) :=
    (isOpen_extChartAt_target (I := ComplexModel n) x).prod isOpen_Ioo
  have hpoint : (chartPt x x, t) ∈ chartTarget x ×ˢ Ioo 0 T := ⟨hz, ht, htT⟩
  have hell := (negative_logDet_contDiffOn o h U P ρ hloc x T).contDiffAt
    (hopen.mem_nhds hpoint)
  have htest : ContDiffAt ℝ ∞ testFn (chartPt x x, t) := hell.sub hφ
  have hcontact : testFn (chartPt x x, t) = ellipsoidLogDet X h T x (chartPt x x) t := by
    have hc := htouch.1
    rw [scalarGap_positive h T x t ⟨ht, htT⟩] at hc
    dsimp [testFn]
    rw [hx, hc]
    simp only [volumeGap]
    ring
  have hcis : ContMDiffAt 𝓘(ℂ, ComplexVector n) (ComplexModel n) ∞
      (chartInv x) (chartPt x x) :=
    (contMDiffOn_extChartAt_symm (I := ComplexModel n) x).contMDiffAt
      ((isOpen_extChartAt_target (I := ComplexModel n) x).mem_nhds hz)
  have hci : ContinuousAt (chartInv x) (chartPt x x) := hcis.continuousAt
  have hmap : ContinuousAt
      (fun p : ComplexVector n × ℝ => (chartInv x p.1, p.2)) (chartPt x x, t) :=
    (ContinuousAt.comp (g := chartInv x)
      (f := fun p : ComplexVector n × ℝ => p.1) hci continuousAt_fst).prodMk continuousAt_snd
  have htouch' : ∀ᶠ p : ComplexVector n × ℝ in 𝓝 (chartPt x x, t),
      scalarGap X h T (chartInv x p.1) p.2 ≤ φ (chartInv x p.1) p.2 := by
    have hm : Tendsto (fun p : ComplexVector n × ℝ => (chartInv x p.1, p.2))
        (𝓝 (chartPt x x, t)) (𝓝 (x, t)) := by
      simpa only [hx] using hmap.tendsto
    exact hm.eventually htouch.2
  have hlower : ∀ᶠ p in 𝓝 (chartPt x x, t),
      testFn p ≤ ellipsoidLogDet X h T x p.1 p.2 := by
    filter_upwards [htouch', hopen.mem_nhds hpoint] with p hp hpO
    rw [scalarGap_fixed_chart h ρ hopt T hT x p.1 p.2 hpO.1 hpO.2] at hp
    dsimp [testFn]
    dsimp only [volumeGap] at hp
    linarith
  have hineq := hcomp T hT x (chartPt x x) t hz ⟨ht, htT⟩ testFn htest hcontact hlower
  have hdφ : HasDerivAt (φ x) (timeDeriv φ x t) t :=
    (smoothNear_time_differentiableAt φ x t hφ).hasDerivAt
  have hd : deriv (fun s => testFn (chartPt x x, s)) t =
      scalarCurvature (h t) x - timeDeriv φ x t := by
    have he := ((negative_logDet_hasDerivAt o h U P ρ hloc x t ht).sub hdφ).deriv
    simpa only [testFn, hx, Pi.sub_def] using he
  have htrace : traceWith (hMat (h t) x (chartPt x x))
      (leviC (fun z => testFn (z, t)) (chartPt x x)) =
      scalarCurvature (h t) x - laplacian (h t) (fun y => φ y t) x := by
    dsimp only [testFn]
    rw [test_difference_levi o h U P ρ hloc x t ht.le φ hφ]
    simp only [traceWith, scalarCurvature, laplacian, Matrix.mul_sub, Matrix.trace_sub,
      Complex.sub_re, gMat]
  rw [hd, htrace] at hineq
  rw [← scalarGap_positive h T x t ⟨ht, htT⟩] at hineq
  exact scalar_gap_test_rearrangement _ _ _ _ hineq

end Yau.NodeProofs.E03Aux
