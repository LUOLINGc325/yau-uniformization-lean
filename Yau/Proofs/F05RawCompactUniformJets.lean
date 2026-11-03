import Yau.Proofs.F05InteriorUniformSchauder
import Yau.Proofs.F05RawChartEllipticity
import Yau.Proofs.F05RawChartPositiveSmooth
import Yau.Proofs.F05RawRelativeEquation
import Yau.Proofs.F05FullJetTimeTranslation
import Yau.Proofs.F05CompactSolutionTimeSlab

/-! A fixed raw reference chart has uniform actual four-jet bounds for
all later compact-domain solutions. Constants precede the changing
solution domain, its atlas, datum, Hölder exponent and finite norm. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_compact_solution_raw_uniform_jets (hn : 0 < n)
    {O : Set M.Carrier} {A : AtlasData M} (hA : GenuineAtlas O A) (i : Fin A.count)
    (h : ℝ → HermitianField M) {T s B : ℝ} (hT : 0 < T) (hs : 0 < s) (hsT : s < T)
    (hB : 0 ≤ B) (hh : MetricFamilySmooth h (Icc 0 T))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 T)) :
    ∃ α C : ℝ, 0 < α ∧ α < 1 ∧ 0 < C ∧
      ∀ (V : Set M.Carrier) (D : AtlasData M), GenuineAtlas V D →
      ∀ p w : M.Carrier → ℝ → ℝ, SmoothSpaceTime p (Icc 0 T) →
      F05CompactDirichletSolution V D h p T w →
      (lift A i '' Metric.ball 0 3 ⊆ closure V) →
      (∀ z ∈ Metric.ball 0 3, ∀ t ∈ Icc 0 T, 0 ≤ w (lift A i z) t ∧ w (lift A i z) t ≤ B) →
      C2 (cylinder (region none (9/4)) s T) (pull A i w) ∧
      HolderBound α (cylinder (region none (9/4)) s T)
        (fun z => ((pull A i w z,spatialD (pull A i w) z),
          (spatialDD (pull A i w) z,timeD (cylinder (region none (9/4)) s T) (pull A i w) z))) C := by
  let σ : ℝ := s/2
  let S : ℝ := T-σ
  let τ : ℝ := s-σ
  have hσ : 0 < σ := by dsimp only [σ]; linarith
  have hσT : σ < T := by dsimp only [σ]; linarith
  have hS : 0 < S := by dsimp only [S]; linarith
  have hτ : 0 < τ := by dsimp only [τ,σ]; linarith
  have hτS : τ < S := by dsimp only [τ,S]; linarith
  have hMap : MapsTo (fun t : ℝ => t+σ) (Icc 0 S) (Icc 0 T) := by
    intro t ht
    dsimp only [S] at ht
    constructor <;> linarith [ht.1,ht.2]
  let hShift : ℝ → HermitianField M := fun t => h (t+σ)
  let RShift : M.Carrier → ℝ → ℝ := F05ManifoldTimeShift σ (fun x t => scalarCurvature (h t) x)
  have hhShift := F05_smooth_metric_time_shift σ hMap h hh
  have hRShift := F05_smooth_spacetime_time_shift σ hMap _ hR
  have hCoeff := F05_flat_coefficients_smooth hA hShift hhShift i
  have hRawR := F05_pull_spacetime_smooth hA RShift hRShift i
  obtain ⟨lam,upper,hEll⟩ := F05_flat_principal_elliptic_radius hA hShift
    (by norm_num : (11/4 : ℝ) < 3) hhShift i
  obtain ⟨α,C0,hα,hα1,hC0,hEstimate⟩ :=
    F05_interior_uniform_schauder hn hS hτ hτS hB hCoeff hRawR hEll
  refine ⟨α,2*C0,hα,hα1,by positivity,?_⟩
  intro V D hD p w hp hw hDomain hRange
  have hFull := F05_compact_solution_positive_smooth hn hD h p w hT hh hp hR hw
  have hSmooth := F05_cross_atlas_raw_shift_smooth hA hD w hσ hσT i hDomain hFull
  let wShift := F05ManifoldTimeShift σ w
  have hSmoothActual : ContDiffOn ℝ ∞ (pull A i wShift) (Metric.ball 0 3 ×ˢ Icc 0 S) := hSmooth
  obtain ⟨β,K,hβ,hβ1,hK,hSch,hCont,h0,hBoundary,hEquation⟩ := hw
  have hShiftEquation := F05_manifold_time_shift_equation hD h hS hMap w
    (fun j => (hSch j).1) hEquation
  have hExp := F05_raw_chart_exp_equation hA hShift RShift wShift hS hhShift i hDomain
    (hSmoothActual.mono (fun z hz => ⟨hz.1,Ioc_subset_Icc_self hz.2⟩)) hShiftEquation
  have hExpFunction : pull A i (fun x t => Real.exp (wShift x t)) =
      (fun z => Real.exp (pull A i wShift z)) := by
    funext z
    rfl
  rw [hExpFunction] at hExp
  have hExpNative : Yau.ParabolicCandidates.ExpDivergenceEquation
      (F05CapOpen none 3 ×ˢ Ioc 0 S)
      (fun z => flatA (hShift z.2) A i z) (fun z j => flatB (hShift z.2) A i z j)
      (pull A i RShift) (fun z => Real.exp (pull A i wShift z)) := by
    simpa only [F05CapOpen,F05FlatOpen,univ_inter] using hExp
  have hLag : 0 < τ/2 := by linarith
  have hLagS : τ/2 < S := by linarith
  have hMapLate : MapsTo (fun t : ℝ => t+σ) (Icc (τ/2) S) (Icc 0 T) :=
    fun t ht => hMap ⟨hLag.le.trans ht.1,ht.2⟩
  have hLateEquation := F05_manifold_time_shift_equation hD h hLagS hMapLate w
    (fun j => (hSch j).1) hEquation
  have hRelEquation := F05_raw_relative_nonlinear_equation hA hShift RShift wShift i hLagS hDomain
    (hSmoothActual.mono (fun z hz => ⟨hz.1,hLag.le.trans hz.2.1,hz.2.2⟩)) hLateEquation
  have hLocalRange (z : Point n) (hz : z ∈ cylinder (region none (11/4)) 0 S) :
      0 ≤ pull A i wShift z ∧ pull A i wShift z ≤ B := by
    have hz3 : z.1 ∈ Metric.ball (0 : Space n) 3 := by
      rw [Metric.mem_ball,dist_zero_right]
      linarith [hz.1.1]
    exact hRange z.1 hz3 (z.2+σ) (hMap hz.2)
  have hRel := hEstimate (pull A i wShift) hSmoothActual hLocalRange hExpNative hRelEquation
  have hDU : region (n := n) none (9/4) ⊆ Metric.ball 0 3 := by
    intro z hz
    rw [Metric.mem_ball,dist_zero_right]
    linarith [hz.1]
  have hShiftC2 := F05_smooth_closed_slab_c2 Metric.isOpen_ball hDU hτS le_rfl
    (hSmoothActual.mono (fun z hz => ⟨hz.1,hτ.le.trans hz.2.1,hz.2.2⟩))
  have hTuple := F05_full_jet_holder_of_relative
    (F05_region_uniqueDiffOn none (by norm_num : (0 : ℝ) < 9/4)) hShiftC2 hRel
  have hBackMap : MapsTo (fun t : ℝ => t+(-σ)) (Icc s T) (Icc τ S) := by
    intro t ht
    dsimp only [τ,S]
    constructor <;> linarith [ht.1,ht.2]
  have hBack := F05_full_jet_holder_time_translation hsT hBackMap hShiftC2 hTuple
  have hBackValue : F05TimeAffine 1 (-σ) (pull A i wShift) = pull A i w := by
    funext z
    simp [F05TimeAffine,F05TimeAffinePoint,pull,wShift,F05ManifoldTimeShift]
  have hRawOriginal := F05_cross_atlas_raw_positive_smooth hA hD w hs hsT i hDomain hFull
  refine ⟨F05_smooth_closed_slab_c2 Metric.isOpen_ball hDU hsT le_rfl hRawOriginal,?_⟩
  simpa only [hBackValue] using hBack

end Yau.Proofs.F05Aux
