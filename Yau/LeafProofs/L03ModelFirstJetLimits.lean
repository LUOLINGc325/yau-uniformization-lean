import Yau.LeafProofs.L03FirstOrderGradientLimits
import Yau.LeafProofs.L03RawChartForms

open MeasureTheory Filter Module
open scoped Topology ContDiff

noncomputable section

namespace Yau.LeafProofs.L03

def basisField {E F α : Type*} [AddCommGroup F] [Module ℝ F] [Fintype α]
    (b : Basis α ℝ F) (u : E → α → ℝ) (x : E) : F := ∑ c, u x c • b c

theorem basisField_coordinates {E F α : Type*} [AddCommGroup F] [Module ℝ F] [Fintype α]
    (b : Basis α ℝ F) (u : E → α → ℝ) (x : E) (c : α) :
    b.repr (basisField b u x) c = u x c := congrFun (b.repr_sum_self (u x)) c

theorem basisField_contDiff {E F α : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] [Fintype α]
    (b : Basis α ℝ F) (u : E → α → ℝ) (hu : ∀ c, ContDiff ℝ ∞ (fun x => u x c)) :
    ContDiff ℝ ∞ (basisField b u) := ContDiff.sum (fun c _ => (hu c).smul contDiff_const)

theorem basisField_tsupport_subset {E F α : Type*} [TopologicalSpace E]
    [AddCommGroup F] [Module ℝ F] [Fintype α]
    (b : Basis α ℝ F) (u : E → α → ℝ) {K : Set E} (hK : IsClosed K)
    (hu : ∀ c, tsupport (fun x => u x c) ⊆ K) : tsupport (basisField b u) ⊆ K := by
  apply closure_minimal _ hK
  intro x hx
  by_contra hn
  have hz (c : α) : u x c = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => u y c) (fun h => hn (hu c h))
  exact hx (by simp only [basisField, hz, zero_smul, Finset.sum_const_zero])

/-- A genuine smooth first-jet calculator has a raw compact L² output
limit along compact smooth fields with strong value/gradient limits.
The calculator itself is the actual fixed CLM field, including off-chart
zero jets; scalar extensions are used only to prove estimates. -/
theorem exists_model_firstJet_output_limit {n : ℕ} {F G α β : Type*}
    [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
    [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G] [Fintype α] [Fintype β]
    (ν : Measure (ComplexVector n)) [IsLocallyFiniteMeasure ν]
    (bi : Basis α ℝ F) (bo : Basis β ℝ G)
    (J : ComplexVector n → (F × (ComplexVector n →L[ℝ] F)) →L[ℝ] G)
    (O : Set (ComplexVector n)) (hO : IsOpen O)
    (hJ : ∀ p, ContDiffOn ℝ ∞ (fun z => J z p) O)
    {K : Set (ComplexVector n)} (hK : IsCompact K) (hKO : K ⊆ O)
    (U : ℕ → ComplexVector n → α → ℝ) (u : ComplexVector n → α → ℝ)
    (D : ComplexVector n → RIdx n × α → ℝ)
    (hU : ∀ m c, ContDiff ℝ ∞ (fun z => U m z c))
    (hUK : ∀ m c, tsupport (fun z => U m z c) ⊆ K)
    (hu : ∀ c, MemLp (fun z => u z c) 2 ν) (huK : ∀ c, tsupport (fun z => u z c) ⊆ K)
    (hD : ∀ q, MemLp (fun z => D z q) 2 ν) (hDK : ∀ q, tsupport (fun z => D z q) ⊆ K)
    (hUt : ∀ c, Tendsto (fun m => ∫ z, ‖U m z c - u z c‖ ^ 2 ∂ν) atTop (𝓝 0))
    (hDt : ∀ i c, Tendsto (fun m => ∫ z,
      ‖fderiv ℝ (fun y => U m y c) z (realModelBasis n i) - D z (i, c)‖ ^ 2 ∂ν) atTop (𝓝 0)) :
    ∃ (P : ℕ → ComplexVector n → G) (W : ComplexVector n → G),
      (∀ m, ContDiff ℝ ∞ (P m)) ∧ (∀ m, tsupport (P m) ⊆ K) ∧
      MemLp W 2 ν ∧ tsupport W ⊆ K ∧
      (∀ m z, P m z = J z (basisField bi (U m) z, fderiv ℝ (basisField bi (U m)) z)) ∧
      Tendsto (fun m => ∫ z, ‖P m z - W z‖ ^ 2 ∂ν) atTop (𝓝 0) := by
  classical
  let q := fun r => (bo.coord r).toContinuousLinearMap
  let a := firstJetDerivativeCoefficient (realModelBasis n) bi q J
  let b := firstJetValueCoefficient bi q J
  obtain ⟨θ, hθ, hcθ, hθO, _, hθK⟩ := exists_model_chart_cutoff hO hK hKO
  let ae := fun r c i z => θ z * a r c i z
  let be := fun r c z => θ z * b r c z
  have ha (r : β) (c : α) (i : RIdx n) : ContDiff ℝ ∞ (ae r c i) :=
    (scalar_cutoff_contDiff_properties hO θ hθ hcθ hθO _
      (firstJetDerivativeCoefficient_contDiffOn (realModelBasis n) bi q J O hJ r c i)).1
  have hb (r : β) (c : α) : ContDiff ℝ ∞ (be r c) :=
    (scalar_cutoff_contDiff_properties hO θ hθ hcθ hθO _
      (firstJetValueCoefficient_contDiffOn bi q J O hJ r c)).1
  choose Ac Kc hAc hKc using fun r c i => compact_contDiff_coefficient_bounds (ae r c i) (ha r c i) hcθ.mul_right
  choose Bc Kb hBc hKb using fun r c => compact_contDiff_coefficient_bounds (be r c) (hb r c) hcθ.mul_right
  have hcU (m : ℕ) (c : α) : HasCompactSupport (fun z => U m z c) :=
    hK.of_isClosed_subset (isClosed_tsupport _) (hUK m c)
  have hUm (m : ℕ) (c : α) : MemLp (fun z => U m z c) 2 ν := (hU m c).continuous.memLp_of_hasCompactSupport (hcU m c)
  have hUd (m : ℕ) (i : RIdx n) (c : α) : MemLp
      (fun z => fderiv ℝ (fun y => U m y c) z (realModelBasis n i)) 2 ν :=
    (((hU m c).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const).continuous.memLp_of_hasCompactSupport
      ((hcU m c).fderiv_apply ℝ (realModelBasis n i))
  have hs (r : β) := firstOrderSystemApply_gradient_limits_tendsto ν (realModelBasis n) ae be
    (fun r c i => (ha r c i).continuous.aestronglyMeasurable) (fun r c => (hb r c).continuous.aestronglyMeasurable)
    Ac hAc Bc hBc U u D hUm hu hUd hD hUt hDt r
  let p := fun m z r => firstOrderSystemApply (realModelBasis n) ae be (U m) z r
  let w := fun z r => firstOrderSystemValueFromJet ae be u D z r
  let P := fun m => basisField bo (p m)
  let W := basisField bo w
  have hp (m : ℕ) (r : β) : ContDiff ℝ ∞ (fun z => p m z r) := by
    exact ContDiff.sum (fun c _ =>
      (ContDiff.sum (fun i _ => (ha r c i).mul
        (((hU m c).fderiv_right (m := ∞) (by simp)).clm_apply contDiff_const))).add ((hb r c).mul (hU m c)))
  have hpK (m : ℕ) (r : β) : tsupport (fun z => p m z r) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hn
    have hzU (c : α) : U m z c = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => U m y c) (fun h => hn (hUK m c h))
    have hzD (c : α) : fderiv ℝ (fun y => U m y c) z = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hn (hUK m c h))
    exact hz (by simp only [p, firstOrderSystemApply, hzU, hzD, zero_apply, mul_zero, Finset.sum_const_zero, zero_add])
  have hwK (r : β) : tsupport (fun z => w z r) ⊆ K := by
    apply closure_minimal _ hK.isClosed
    intro z hz
    by_contra hn
    have hzu (c : α) : u z c = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => u y c) (fun h => hn (huK c h))
    have hzD (s : RIdx n × α) : D z s = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => D y s) (fun h => hn (hDK s h))
    exact hz (by simp only [w, firstOrderSystemValueFromJet, hzu, hzD, mul_zero, Finset.sum_const_zero, zero_add])
  have hPK (m : ℕ) : tsupport (P m) ⊆ K := basisField_tsupport_subset bo (p m) hK.isClosed (hpK m)
  have hWK : tsupport W ⊆ K := basisField_tsupport_subset bo w hK.isClosed hwK
  have hWm : MemLp W 2 ν := memLp_finsetSum (f := fun r z => w z r • bo r) Finset.univ
    (fun r _ => (ContinuousLinearMap.toSpanSingleton ℝ (bo r)).comp_memLp' (hs r).2.1)
  refine ⟨P, W, fun m => basisField_contDiff bo (p m) (hp m), hPK, hWm, hWK, ?_, ?_⟩
  · intro m z
    apply bo.repr.injective
    ext r
    rw [basisField_coordinates]
    have hjet := firstOrderSystemApply_eq_firstJet (realModelBasis n) bi q J
      (basisField bi (U m)) z ((basisField_contDiff bi (U m) (hU m)).differentiable (by simp) z) r
    have hcoord : (fun y c => bi.repr (basisField bi (U m) y) c) = U m := by
      funext y c
      exact basisField_coordinates bi (U m) y c
    rw [hcoord] at hjet
    by_cases hz : z ∈ K
    · simpa only [p, firstOrderSystemApply, ae, be, (hθK z hz).1, one_mul, q,
        LinearMap.coe_toContinuousLinearMap', Basis.coord_apply] using hjet
    · have hzP : P m z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hPK m h))
      have hGsup := basisField_tsupport_subset bi (U m) hK.isClosed (hUK m)
      have hzG : basisField bi (U m) z = 0 := image_eq_zero_of_notMem_tsupport (fun h => hz (hGsup h))
      have hzD : fderiv ℝ (basisField bi (U m)) z = 0 := fderiv_of_notMem_tsupport ℝ (fun h => hz (hGsup h))
      have hzpc : p m z r = 0 := image_eq_zero_of_notMem_tsupport (f := fun y => p m y r) (fun h => hz (hpK m r h))
      simp only [hzpc, hzG, hzD, ← Prod.zero_eq_mk, map_zero, Finsupp.zero_apply]
  · have hv := integral_sq_tendsto_zero_of_basis_coordinates ν bo (fun m z => P m z - W z)
      (fun m r => (((hs r).1 m).sub (hs r).2.1).ae_eq
        (Filter.Eventually.of_forall fun z => by
          simp only [Pi.sub_apply, P, W, map_sub, Finsupp.sub_apply, basisField_coordinates, p, w]))
      (fun r => by simpa only [P, W, map_sub, Finsupp.sub_apply, basisField_coordinates, p, w, Pi.sub_apply] using (hs r).2.2)
    exact hv.2

end Yau.LeafProofs.L03
