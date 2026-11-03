import Yau.Proofs.F05BootstrapBufferedLocalEstimate
import Yau.Proofs.F05BootstrapBase
import Yau.Proofs.F05BootstrapSchauderLinear
import Yau.Proofs.F05BootstrapRelativeCongruence
import Yau.Proofs.F05ValueCoefficientBudget
import Yau.Proofs.F05DirichletEquation

/-! The original nonlinear solution has a uniform positive-time physical
Schauder bound from its value Hölder bound alone. All constants precede
both the endpoint and candidate; no derivative budget is supplied. -/

open Set
open scoped ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.F05Transport Yau.LeafProofs.L16Aux
variable {n : ℕ} {M : ComplexManifold n}

theorem F05_nonlinear_inner_schauder_uniform {O : Set M.Carrier} {A : AtlasData M}
    (hA : GenuineAtlas O A) (h : ℝ → HermitianField M) (p : M.Carrier → ℝ → ℝ)
    {S D α s : ℝ} (hS : 0 < S) (hh : MetricFamilySmooth h (Icc 0 S))
    (hp : SmoothSpaceTime p (Icc 0 S))
    (hR : SmoothSpaceTime (fun x t => scalarCurvature (h t) x) (Icc 0 S))
    (hD : 0 ≤ D) (hα : 0 < α) (hα1 : α < 1) (hs : 0 < s) (hsS : s < S) :
    ∃ C : ℝ, 0 < C ∧ ∀ T : ℝ, s < T → T ≤ S → ∀ w : M.Carrier → ℝ → ℝ,
      (∀ i, C2 (F05Q A i T) (pull A i w)) →
      (∀ i, HolderBound α (F05Q A i T) (pull A i w) D) →
      (∀ x ∈ frontier O, ∀ t ∈ Icc 0 T, w x t = p x t) →
      (∀ x ∈ closure O, ∀ t ∈ Icc 0 T,
        derivWithin (w x) (Icc 0 T) t = Real.exp (-w x t)*laplacian (h t) (fun y => w y t) x+
          (1-Real.exp (-w x t))*scalarCurvature (h t) x) →
      ∀ i, F05RelSchauder α (region (A.normal i) (3/2)) (Icc s T) (pull A i w) C := by
  classical
  obtain ⟨lam,upper,M0,hM0,hCoeff⟩ := F05_value_nonlinear_coefficient_budgets hA h hS hh hD
  obtain ⟨F,hF,hSource⟩ := F05_value_dirichlet_source_budgets hA h p hS hh hp hR hD
  obtain ⟨K,hK,hPBudget⟩ := F05_smooth_schauder_uniform hA p hS hp
  let χ : ContDiffBump (0 : Space n) := ⟨7/4,15/8,by norm_num,by norm_num⟩
  have hχ : χ.rOut ≤ (2 : ℝ) := by norm_num [χ]
  have hLocal (i : Fin A.count) := F05_buffered_physical_local_schauder
    (M := M0) (lam := lam) (upper := upper) (A.normal i) χ hχ hα hα1 hM0.le
    (by norm_num : (0 : ℝ) < 3/2) (by norm_num [χ] : (3/2 : ℝ) < χ.rIn) hs
  choose C0 hC0 hEstimate using hLocal
  have hPSch (i : Fin A.count) :=
    F05_native_schauder_local_relative (A.normal i) hα hα1 (hPBudget α hα hα1 S hS le_rfl i)
      (3/2) (by norm_num) (by norm_num) s hs hsS
  choose CP hCP hPInner using hPSch
  let C := 1+∑ i,(C0 i*(D+K+F)+CP i)
  have hTerms (i : Fin A.count) : 0 ≤ C0 i*(D+K+F)+CP i :=
    add_nonneg (mul_nonneg (hC0 i).le (add_nonneg (add_nonneg hD hK.le) hF.le)) (hCP i).le
  have hC : 0 < C := by
    have hSum := Finset.sum_nonneg (fun i (_ : i ∈ (Finset.univ : Finset (Fin A.count))) => hTerms i)
    dsimp only [C]
    linarith
  refine ⟨C,hC,?_⟩
  intro T hsT hTS w hw hValue hBoundary hEquation i
  have hT : 0 < T := hs.trans hsT
  have hp2 := F05_smooth_actual_chart_c2 hA hp hT hTS i
  have hV := c2_sub (hw i) hp2
  have hPhysical := hCoeff α hα hα1 T hTS w hValue i
  have hVBound : ∀ z ∈ F05Q A i T, |pull A i w z-pull A i p z| ≤ D+K := by
    intro z hz
    simpa only [Real.norm_eq_abs] using (norm_sub_le _ _).trans
      (add_le_add ((hValue i).2.1 z hz) ((hPBudget α hα hα1 T hT hTS i).2.2.1 z hz).1)
  have hFace : ∀ j, A.normal i = some j → ∀ x ∈ region (A.normal i) 2, realCoord x j = 0 →
      ∀ t ∈ Icc 0 T, pull A i w (x,t)-pull A i p (x,t) = 0 := by
    intro j hj x hx hx0 t ht
    have hPhysical := ((hA.1 i).2.2.2.2.2.2.2 x (F05D_mem_ball hx)).2.2
    have hFront : lift A i x ∈ frontier O := hPhysical.mpr (by simpa only [hj] using hx0)
    exact sub_eq_zero.mpr (hBoundary (lift A i x) hFront t ht)
  have hSchV := hEstimate i T
    (F05FlowPrincipal A i h (fun x t => Real.exp (-w x t)))
    (F05FlowDrift A i h (fun x t => Real.exp (-w x t)))
    (pull A i (F05DirichletForcing h T p w)) (fun z => pull A i w z-pull A i p z)
    F (D+K) hsT hPhysical.1 hPhysical.2.1 hPhysical.2.2
    (hSource α hα hα1 T hT hTS w hValue i)
    (F05_native_c2_to_relative (F05_region_uniqueDiffOn (A.normal i) (by norm_num)) hV)
    hVBound hFace (F05_dirichlet_relative_equation hA h p w T i hp2 (hw i) hEquation)
  have hPInnerT := F05_relative_schauder_restrict
    (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 3/2))
    (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 3/2))
    (uniqueDiffOn_Icc hsT) subset_rfl (show Icc s T ⊆ Icc s S from fun t ht => ⟨ht.1,ht.2.trans hTS⟩)
    (hPInner i)
  have hSum := F05_relative_schauder_add
    (F05_region_uniqueDiffOn (A.normal i) (by norm_num : (0 : ℝ) < 3/2)) hSchV hPInnerT
  have hActual : F05RelSchauder α (region (A.normal i) (3/2)) (Icc s T)
      (pull A i w) (C0 i*(D+K+F)+CP i) :=
    F05_relative_schauder_congr hSum (fun z hz => by ring)
  have hCi : C0 i*(D+K+F)+CP i ≤ C := by
    have hSingle := Finset.single_le_sum (fun j (_ : j ∈ (Finset.univ : Finset (Fin A.count))) => hTerms j)
      (Finset.mem_univ i)
    dsimp only [C]
    linarith
  exact ⟨hActual.1,holderBound_mono_const hActual.2.1 hCi,
    holderBound_mono_const hActual.2.2.1 hCi,holderBound_mono_const hActual.2.2.2 hCi⟩

end Yau.Proofs.F05Aux
