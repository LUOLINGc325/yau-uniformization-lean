import Yau.Proofs.F05BootstrapHolderLimit
import Yau.Proofs.F05BootstrapWeight
import Mathlib.Topology.ContinuousMap.Bounded.ArzelaAscoli

/-! A uniformly bounded parabolic Hölder family has a uniformly convergent
subsequence on a compact cylinder. The subsequence is constructed by the
actual Arzelà–Ascoli theorem in the proper finite-dimensional target. -/

open Set Filter
open scoped Topology
noncomputable section
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types true
namespace Yau.Proofs.F05Aux
open Yau.Parabolic Yau.LeafProofs.L16Aux

theorem F05_holder_family_equicontinuous {n : ℕ} {V ι : Type*}
    [NormedAddCommGroup V] {α C : ℝ} (hα : 0 < α) {Q : Set (Point n)}
    (f : ι → Q → V)
    (hPair : ∀ i p q, ‖f i p-f i q‖ ≤ C*holderWeight α p.val q.val) :
    Equicontinuous f := by
  intro p
  have hConst : Continuous (fun _ : Q => C) := continuous_const
  have hWeight : Continuous (fun q : Q => C*holderWeight α p.val q.val) :=
    hConst.mul (F05_holderWeight_fixed_continuous hα.le p.val Q)
  have hZero : C*holderWeight α p.val p.val = 0 := by
    rw [F05_holderWeight_diagonal hα,mul_zero]
  have hTendsto : Tendsto (fun q : Q => C*holderWeight α p.val q.val) (𝓝 p) (𝓝 0) := by
    simpa only [hZero] using (hWeight.continuousAt (x := p)).tendsto
  have hBound : ∀ᶠ q : Q in 𝓝 p, ∀ i, dist (f i p) (f i q) ≤ C*holderWeight α p.val q.val :=
    Eventually.of_forall (fun q i => by simpa only [dist_eq_norm] using hPair i p q)
  exact Metric.equicontinuousAt_of_continuity_modulus
    (fun q : Q => C*holderWeight α p.val q.val) hTendsto f hBound

theorem F05_holder_compact_subsequence {n : ℕ} {V : Type*}
    [NormedAddCommGroup V] [ProperSpace V] {α C : ℝ} (hα : 0 < α)
    {Q : Set (Point n)} (hQ : IsCompact Q) {f : ℕ → Point n → V}
    (hf : ∀ k, HolderBound α Q (f k) C) :
    ∃ (φ : ℕ → ℕ) (g : Point n → V), StrictMono φ ∧
      TendstoUniformlyOn (fun k => f (φ k)) g atTop Q := by
  classical
  letI : CompactSpace Q := isCompact_iff_compactSpace.mp hQ
  let F : ℕ → BoundedContinuousFunction Q V := fun k => BoundedContinuousFunction.mkOfCompact
    ⟨fun z => f k z.val,(holderBound_continuousOn hα (hf k)).domRestrict⟩
  have hIn : ∀ (g : BoundedContinuousFunction Q V) (z : Q), g ∈ range F → g z ∈ Metric.closedBall 0 C := by
    intro g z hg
    obtain ⟨k,rfl⟩ := hg
    rw [Metric.mem_closedBall,dist_zero_right]
    change ‖f k z.val‖ ≤ C
    exact (hf k).2.1 z.val z.property
  have hEqui : Equicontinuous (fun g : range F => (g.val : Q → V)) := by
    apply F05_holder_family_equicontinuous hα
    intro g p q
    obtain ⟨k,hk⟩ := g.property
    rw [← hk]
    exact (hf k).2.2 p.val p.property q.val q.property
  have hCompact := BoundedContinuousFunction.arzela_ascoli
    (Metric.closedBall (0 : V) C) (isCompact_closedBall 0 C) (range F) hIn hEqui
  obtain ⟨g,hg,φ,hφ,hConv⟩ := hCompact.tendsto_subseq (fun k => subset_closure (mem_range_self k))
  have hUniform := BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hConv
  let gFull : Point n → V := fun z => if hz : z ∈ Q then g ⟨z,hz⟩ else 0
  refine ⟨φ,gFull,hφ,?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformly_iff.mp hUniform ε hε] with k hk z hz
  have hkz := hk ⟨z,hz⟩
  change dist (g ⟨z,hz⟩) (f (φ k) z) < ε at hkz
  simpa only [gFull,dite_eq_left hz] using hkz

end Yau.Proofs.F05Aux
