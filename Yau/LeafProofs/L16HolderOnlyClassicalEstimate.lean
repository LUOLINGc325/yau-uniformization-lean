import Yau.LeafProofs.L16HolderOnlyInverse
import Yau.LeafProofs.L16SpatialBootstrap

open MeasureTheory Filter
open scoped Topology ContDiff Matrix Matrix.Norms.Frobenius
noncomputable section
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L16Aux
open Yau.Parabolic Yau.ParabolicCandidates

/-- The constructed inverse upgrades every bounded classical zero-initial
    solution, using bounded uniqueness rather than a prior Schauder norm. -/
theorem exists_uniform_short_classical_schauder_estimate_holder_only {n : ℕ}
    {α M lam upper : ℝ} (hα : 0 < α) (hα1 : α < 1)
    {K : Set (Space n)} (hK : IsCompact K) :
    ∃ δ C : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 < C ∧
      ∀ (T : ℝ) (a : Point n → Mat n) (b : Point n → Yau.RIdx n → ℝ)
        (f u : Point n → ℝ) (F B : ℝ),
      0 < T → T ≤ δ → HolderBound α (cylinder Set.univ 0 T) a M →
      (∀ i, HolderBound α (cylinder Set.univ 0 T) (fun p => b p i) M) →
      Elliptic (cylinder Set.univ 0 T) a lam upper →
      (∀ p ∈ cylinder Set.univ 0 T, p.1 ∉ K → a p = 1) →
      HolderBound α (cylinder Set.univ 0 T) f F →
      C2 (cylinder Set.univ 0 T) u →
      (∀ p ∈ cylinder Set.univ 0 T, |u p| ≤ B) →
      (∀ x, u (x,0) = 0) →
      (∀ p ∈ cylinder Set.univ 0 T, linearOp (cylinder Set.univ 0 T) a b u p = f p) →
      SchauderBound α (cylinder Set.univ 0 T) u (C*F) ∧
      HolderBound α (cylinder Set.univ 0 T) (fun p => (u p,spatialD u p)) (C*F) := by
  obtain ⟨δ,C,hδ,hδ1,hC,hInverse⟩ :=
    exists_uniform_short_schauder_inverse_holder_only (n := n) (M := M)
      (lam := lam) (upper := upper) hα hα1 hK
  refine ⟨δ,C,hδ,hδ1,hC,?_⟩
  intro T a b f u F B hT hTδ ha hb hEll hExterior hf hu hUBound hInit hPDE
  obtain ⟨v,hv,hvLow,hvInit,hvPDE⟩ := hInverse T a b hT hTδ ha hb hEll hExterior f F hf
  have hEq : Set.EqOn v u (cylinder Set.univ 0 T) := by
    apply bounded_wholeSpace_unique hT hv.1 hu hEll ha.1
      (fun p hp i => by simpa only [Real.norm_eq_abs] using (hb i).2.1 p hp)
      (fun p hp => (hv.2.2.1 p hp).1) hUBound
      (fun x => by rw [hvInit x,hInit x])
    intro p hp
    have hpQ : p ∈ cylinder Set.univ 0 T := ⟨hp.1,hp.2.1.le,hp.2.2⟩
    rw [hvPDE p hpQ,hPDE p hpQ]
  exact ⟨schauderBound_congr_cylinder_univ hv hEq,
    lowPair_holderBound_congr_cylinder_univ hvLow hEq⟩

end Yau.LeafProofs.L16Aux
