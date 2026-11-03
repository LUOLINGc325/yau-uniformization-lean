import Yau.Proofs.P06HodgeRegularityWeakSums
import Yau.Proofs.P06HodgeRegularityScalarEnergy
import Yau.Proofs.P06HodgeRegularityTestAlgebra
import Yau.LeafProofs.L03DivergenceLocalize

/-! Localizing a rough formal equation requires only value data.
All cutoff commutator coefficients are actual compact smooth tests. -/
noncomputable section
open MeasureTheory Filter
open scoped Topology ContDiff

namespace Yau.NodeProofs.P06Aux
open Yau.LeafProofs.L03

variable {E ι α : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Fintype ι] [Fintype α]

theorem regularitySum_tsupport_subset {γ : Type*} [Fintype γ]
    (F : γ → E → ℝ) {K : Set E} (hK : IsClosed K)
    (hF : ∀ c, tsupport (F c) ⊆ K) :
    tsupport (fun z => ∑ c, F c z) ⊆ K := by
  apply closure_minimal _ hK
  intro z hz
  by_contra hzK
  apply hz
  apply Finset.sum_eq_zero
  intro c _
  exact image_eq_zero_of_notMem_tsupport (fun h => hzK (hF c h))

theorem regularityLocalizedValue_test
    (v : ι → E) (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j)) (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    {O : Set E} {χ : E → ℝ} (hχ : regularityTest O χ) (r c : α) :
    regularityTest O (fun z => localizedDivergenceValueCoefficient v a B χ z r c) := by
  unfold localizedDivergenceValueCoefficient
  apply regularityTest_add
  · apply regularityTest_sum
    intro i
    apply regularityTest_sum
    intro j
    apply regularityTest_add
    · exact regularityTest_coeff_mul (regularityTest_direction hχ (v i))
        (regularityDirection_contDiff (ha r c i j) (v j))
    · exact regularityTest_coeff_mul
        (regularityTest_direction (regularityTest_direction hχ (v i)) (v j)) (ha r c i j)
  · apply regularityTest_sum
    intro i
    exact regularityTest_coeff_mul (regularityTest_direction hχ (v i)) (hB r c i)

theorem regularityLocalizedFlux_test
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    {O : Set E} {χ : E → ℝ} (hχ : regularityTest O χ) (r c : α) (l : ι) :
    regularityTest O (fun z => localizedDivergenceFluxCoefficient v a χ z r c l) := by
  unfold localizedDivergenceFluxCoefficient
  apply regularityTest_sub
  · apply regularityTest_neg
    apply regularityTest_sum
    intro j
    exact regularityTest_coeff_mul (regularityTest_direction hχ (v j)) (ha r c l j)
  · apply regularityTest_sum
    intro i
    exact regularityTest_mul (regularityTest_direction hχ (v i)) (ha r c i l)

def regularityFormalCutoffValue (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (B : α → α → ι → E → ℝ) (χ : E → ℝ) (U W : E → α → ℝ) (z : E) (r : α) : ℝ :=
  χ z * W z r + ∑ c, localizedDivergenceValueCoefficient v a B χ z r c * U z c

def regularityFormalCutoffFlux (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (χ : E → ℝ) (U : E → α → ℝ) (z : E) (r : α) (i : ι) : ℝ :=
  ∑ c, localizedDivergenceFluxCoefficient v a χ z r c i * U z c

theorem regularityFormalCutoffValue_memLp
    (ν : Measure E) [IsLocallyFiniteMeasure ν]
    (v : ι → E) (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j)) (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    {O : Set E} (hO : IsOpen O) {χ : E → ℝ} (hχ : regularityTest O χ)
    (U W : E → α → ℝ)
    (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O))
    (hW : ∀ r, MemLp (fun z => W z r) 2 (ν.restrict O)) (r : α) :
    MemLp (fun z => regularityFormalCutoffValue v a B χ U W z r) 2 ν := by
  apply MemLp.add (regularityCompact_mul_memLp ν hO hχ.1 hχ.2.1 hχ.2.2 (hW r))
  apply memLp_finsetSum Finset.univ
  intro c _
  have ht := regularityLocalizedValue_test v a B ha hB hχ r c
  exact regularityCompact_mul_memLp ν hO ht.1 ht.2.1 ht.2.2 (hU c)

theorem regularityFormalCutoffFlux_memLp
    (ν : Measure E) [IsLocallyFiniteMeasure ν]
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    {O : Set E} (hO : IsOpen O) {χ : E → ℝ} (hχ : regularityTest O χ)
    (U : E → α → ℝ) (hU : ∀ c, MemLp (fun z => U z c) 2 (ν.restrict O)) (r : α) (i : ι) :
    MemLp (fun z => regularityFormalCutoffFlux v a χ U z r i) 2 ν := by
  apply memLp_finsetSum Finset.univ
  intro c _
  have ht := regularityLocalizedFlux_test v a ha hχ r c i
  exact regularityCompact_mul_memLp ν hO ht.1 ht.2.1 ht.2.2 (hU c)

theorem regularityFormalCutoffValue_tsupport
    (v : ι → E) (a : α → α → ι → ι → E → ℝ) (B : α → α → ι → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j)) (hB : ∀ r c i, ContDiff ℝ ∞ (B r c i))
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (U W : E → α → ℝ) (r : α) :
    tsupport (fun z => regularityFormalCutoffValue v a B χ U W z r) ⊆ tsupport χ := by
  apply (tsupport_add _ _).trans
  apply Set.union_subset tsupport_mul_subset_left
  apply regularitySum_tsupport_subset _ (isClosed_tsupport χ)
  intro c
  exact tsupport_mul_subset_left.trans
    (regularityLocalizedValue_test v a B ha hB ⟨hχ,hcχ,Set.Subset.rfl⟩ r c).2.2

theorem regularityFormalCutoffFlux_tsupport
    (v : ι → E) (a : α → α → ι → ι → E → ℝ)
    (ha : ∀ r c i j, ContDiff ℝ ∞ (a r c i j))
    {χ : E → ℝ} (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (U : E → α → ℝ) (r : α) (i : ι) :
    tsupport (fun z => regularityFormalCutoffFlux v a χ U z r i) ⊆ tsupport χ := by
  apply regularitySum_tsupport_subset _ (isClosed_tsupport χ)
  intro c
  exact tsupport_mul_subset_left.trans
    (regularityLocalizedFlux_test v a ha ⟨hχ,hcχ,Set.Subset.rfl⟩ r c i).2.2

end Yau.NodeProofs.P06Aux
