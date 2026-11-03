import Yau.LeafProofs.L17LocalizedSchauderFinite
import Yau.LeafProofs.L17HolderSpace
import Mathlib.Data.Set.Card

open Set Metric Filter
open scoped Topology
noncomputable section
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L17LocalizedSchauderAux
open Yau.LeafProofs.L17Aux Yau.LeafProofs.L17HolderAux

variable {n : ℕ} {M : ComplexManifold n} {g : HermitianField M}

theorem exists_active_neighborhood (P : UniformChartPartition g) (x : M.Carrier) :
    ∃ I : Finset P.centers, I.card ≤ P.overlapBudget ∧
      ∀ᶠ y in 𝓝 x, ∀ p, p ∉ I → y ∉ P.charts.chart p '' closedBall 0 P.radius := by
  classical
  obtain ⟨V,hV,hFinite,hCard⟩ := P.overlap x
  refine ⟨hFinite.toFinset,?_,?_⟩
  · exact (Set.ncard_eq_toFinset_card _ hFinite).symm.le.trans hCard
  · filter_upwards [hV] with y hy p hp hImage
    exact hp (hFinite.mem_toFinset.mpr ⟨y,hImage,hy⟩)

theorem exists_active_finset (P : UniformChartPartition g) (x : M.Carrier) :
    ∃ I : Finset P.centers, I.card ≤ P.overlapBudget ∧
      ∀ p, p ∉ I → x ∉ P.charts.chart p '' closedBall 0 P.radius := by
  obtain ⟨I,hI,hNear⟩ := exists_active_neighborhood P x
  exact ⟨I,hI,hNear.self_of_nhds⟩

theorem continuous_supported_finsum (P : UniformChartPartition g) (T : ℝ)
    {F : Type*} [NormedAddCommGroup F] (f : P.centers → Cylinder M T → F)
    (hf : ∀ p, Continuous (f p))
    (hSupp : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → f p q = 0) :
    Continuous (fun q => ∑ᶠ p, f p q) := by
  rw [continuous_iff_continuousAt]
  intro q
  obtain ⟨I,hI,hNear⟩ := exists_active_neighborhood P q.1
  apply continuousAt_finsum f I (fun p _ => (hf p).continuousAt)
  filter_upwards [continuous_fst.continuousAt.eventually hNear] with r hr p hp
  exact hSupp p r (hr p hp)

theorem norm_supported_finsum_le (P : UniformChartPartition g) (T : ℝ)
    {F : Type*} [NormedAddCommGroup F] (f : P.centers → Cylinder M T → F) (B : ℝ) (hB0 : 0 ≤ B)
    (hSupp : ∀ (p : P.centers) q, q.1 ∉ P.charts.chart p '' closedBall 0 P.radius → f p q = 0)
    (hB : ∀ p q, ‖f p q‖ ≤ B) (q : Cylinder M T) :
    ‖∑ᶠ p, f p q‖ ≤ (P.overlapBudget : ℝ)*B := by
  obtain ⟨I,hI,hActive⟩ := exists_active_finset P q.1
  apply (norm_finsum_le (fun p => f p q) I B
    (fun p hp => hSupp p q (hActive p hp)) (fun p _ => hB p q)).trans
  exact mul_le_mul_of_nonneg_right (by exact_mod_cast hI) hB0

end Yau.LeafProofs.L17LocalizedSchauderAux
