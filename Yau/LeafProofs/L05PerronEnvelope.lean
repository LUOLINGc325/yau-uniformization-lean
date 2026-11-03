import Yau.LeafProofs.L05PerronCalculus
import Mathlib.Topology.Order.MonotoneConvergence

noncomputable section
open Filter MeasureTheory
open scoped Topology ContDiff InnerProductSpace Matrix Matrix.Norms.Frobenius
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

def perronLocalUpper {n : ℕ} (C : Set (Point n)) (u : Point n → ℝ) (p : Point n) (k : ℕ) : ℝ :=
  sSup (u '' (C ∩ Metric.ball p (((k:ℝ)+1)⁻¹)))

def perronUpper {n : ℕ} (C : Set (Point n)) (u : Point n → ℝ) (p : Point n) : ℝ :=
  sInf (Set.range (perronLocalUpper C u p))

def perronLower {n : ℕ} (C : Set (Point n)) (u : Point n → ℝ) (p : Point n) : ℝ :=
  -perronUpper C (fun q => -u q) p

def perronFamilySup {n : ℕ} (S : Set (Point n → ℝ)) (p : Point n) : ℝ :=
  sSup {r | ∃ w∈S, r=w p}

theorem perron_localUpper_nonempty {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ}
    {p : Point n} (hp : p∈C) (k : ℕ) :
    (u '' (C ∩ Metric.ball p (((k:ℝ)+1)⁻¹))).Nonempty := by
  exact ⟨u p,p,⟨hp,Metric.mem_ball_self (by positivity)⟩,rfl⟩

theorem perron_localUpper_bdd {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) (p : Point n) (k : ℕ) :
    BddAbove (u '' (C ∩ Metric.ball p (((k:ℝ)+1)⁻¹))) := by
  refine ⟨M,?_⟩
  rintro r ⟨q,hq,rfl⟩
  exact (abs_le.mp (hb q hq.1)).2

theorem perron_localUpper_bounds {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) (k : ℕ) :
    u p≤perronLocalUpper C u p k ∧ perronLocalUpper C u p k≤M := by
  constructor
  · exact le_csSup (perron_localUpper_bdd hb p k)
      (Set.mem_image_of_mem u ⟨hp,Metric.mem_ball_self (by positivity)⟩)
  · apply csSup_le (perron_localUpper_nonempty hp k)
    rintro r ⟨q,hq,rfl⟩
    exact (abs_le.mp (hb q hq.1)).2

theorem perron_levels_bddBelow {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) :
    BddBelow (Set.range (perronLocalUpper C u p)) := by
  refine ⟨u p,?_⟩
  rintro r ⟨k,rfl⟩
  exact (perron_localUpper_bounds hb hp k).1

theorem perron_upper_le_local {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) (k : ℕ) :
    perronUpper C u p≤perronLocalUpper C u p k :=
  csInf_le (perron_levels_bddBelow hb hp) (Set.mem_range_self k)

theorem perron_upper_bounds {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) :
    u p≤perronUpper C u p ∧ |perronUpper C u p|≤M := by
  have hlo : u p≤perronUpper C u p := by
    apply le_csInf (Set.range_nonempty (perronLocalUpper C u p))
    rintro r ⟨k,rfl⟩
    exact (perron_localUpper_bounds hb hp k).1
  refine ⟨hlo,abs_le.mpr ⟨?_,?_⟩⟩
  · exact (abs_le.mp (hb p hp)).1.trans hlo
  · exact (perron_upper_le_local hb hp 0).trans (perron_localUpper_bounds hb hp 0).2

theorem perron_localUpper_antitone {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) : Antitone (perronLocalUpper C u p) := by
  intro k j hkj
  have hr : ((j:ℝ)+1)⁻¹≤((k:ℝ)+1)⁻¹ := by
    simpa only [one_div] using one_div_le_one_div_of_le (show (0:ℝ)<(k:ℝ)+1 by positivity)
      (show (k:ℝ)+1≤(j:ℝ)+1 by exact_mod_cast Nat.add_le_add_right hkj 1)
  apply csSup_le (perron_localUpper_nonempty hp j)
  rintro r ⟨q,hq,rfl⟩
  exact le_csSup (perron_localUpper_bdd hb p k)
    (Set.mem_image_of_mem u ⟨hq.1,Metric.ball_subset_ball hr hq.2⟩)

theorem perron_localUpper_tendsto {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) :
    Tendsto (perronLocalUpper C u p) atTop (𝓝 (perronUpper C u p)) := by
  exact tendsto_atTop_ciInf (perron_localUpper_antitone hb hp) (perron_levels_bddBelow hb hp)

theorem perron_upper_recovery {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) :
    ∃ q : ℕ → Point n, (∀ k, q k∈C) ∧ Tendsto q atTop (𝓝 p) ∧
      Tendsto (fun k => u (q k)) atTop (𝓝 (perronUpper C u p)) := by
  have hchoose (k : ℕ) : ∃ q∈C ∩ Metric.ball p (((k:ℝ)+1)⁻¹),
      perronLocalUpper C u p k-((k:ℝ)+1)⁻¹<u q := by
    have hr : 0<((k:ℝ)+1)⁻¹ := by positivity
    obtain ⟨r,⟨q,hq,rfl⟩,hv⟩ := exists_lt_of_lt_csSup (perron_localUpper_nonempty hp k)
      (show perronLocalUpper C u p k-((k:ℝ)+1)⁻¹<perronLocalUpper C u p k by linarith)
    exact ⟨q,hq,hv⟩
  choose q hq hval using hchoose
  have hr0 : Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hqdist : Tendsto (fun k => dist (q k) p) atTop (𝓝 0) :=
    squeeze_zero (fun k => dist_nonneg) (fun k => (Metric.mem_ball.mp (hq k).2).le) hr0
  have ht : Tendsto q atTop (𝓝 p) := tendsto_iff_dist_tendsto_zero.mpr hqdist
  have hupper (k : ℕ) : u (q k)≤perronLocalUpper C u p k :=
    le_csSup (perron_localUpper_bdd hb p k) (Set.mem_image_of_mem u (hq k))
  have hgap : Tendsto (fun k => perronLocalUpper C u p k-u (q k)) atTop (𝓝 0) := by
    apply squeeze_zero (fun k => sub_nonneg.mpr (hupper k)) _ hr0
    intro k
    linarith [hval k]
  refine ⟨q,fun k => (hq k).1,ht,?_⟩
  have hh := (perron_localUpper_tendsto hb hp).sub hgap
  simpa only [sub_sub_cancel,sub_zero] using hh

theorem perron_upper_usc {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) : UpperSemicontinuousOn (perronUpper C u) C := by
  intro p hp c hpc
  obtain ⟨r,⟨k,rfl⟩,hkc⟩ := exists_lt_of_csInf_lt
    (Set.range_nonempty (perronLocalUpper C u p)) hpc
  have hrk : 0<((k:ℝ)+1)⁻¹/2 := by positivity
  have hr0 : Tendsto (fun j : ℕ => ((j:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hev : ∀ᶠ j : ℕ in atTop, ((j:ℝ)+1)⁻¹<((k:ℝ)+1)⁻¹/2 := hr0 (eventually_lt_nhds hrk)
  obtain ⟨j,hj⟩ := hev.exists
  have hnear : Metric.ball p (((k:ℝ)+1)⁻¹/2)∈𝓝[C] p :=
    nhdsWithin_le_nhds (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hrk))
  filter_upwards [self_mem_nhdsWithin,hnear] with q hq hqp
  have hlevels : perronLocalUpper C u q j≤perronLocalUpper C u p k := by
    apply csSup_le (perron_localUpper_nonempty hq j)
    rintro a ⟨x,hx,rfl⟩
    have hxp : x∈Metric.ball p (((k:ℝ)+1)⁻¹) := by
      have ht := dist_triangle x q p
      have hxq := Metric.mem_ball.mp hx.2
      have hqp' := Metric.mem_ball.mp hqp
      rw [Metric.mem_ball]
      linarith
    exact le_csSup (perron_localUpper_bdd hb p k) (Set.mem_image_of_mem u ⟨hx.1,hxp⟩)
  exact ((perron_upper_le_local hb hq j).trans hlevels).trans_lt hkc

theorem perron_lower_bounds {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) :
    perronLower C u p≤u p ∧ |perronLower C u p|≤M := by
  have hbneg : ∀ q∈C, |-u q|≤M := fun q hq => by simpa only [abs_neg] using hb q hq
  have hh := perron_upper_bounds hbneg hp
  dsimp only [perronLower]
  constructor
  · linarith [hh.1]
  · simpa only [abs_neg] using hh.2

theorem perron_lower_lsc {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) : LowerSemicontinuousOn (perronLower C u) C := by
  have hbneg : ∀ q∈C, |-u q|≤M := fun q hq => by simpa only [abs_neg] using hb q hq
  exact (perron_upper_usc hbneg).neg

theorem perron_lower_recovery {n : ℕ} {C : Set (Point n)} {u : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) {p : Point n} (hp : p∈C) :
    ∃ q : ℕ → Point n, (∀ k, q k∈C) ∧ Tendsto q atTop (𝓝 p) ∧
      Tendsto (fun k => u (q k)) atTop (𝓝 (perronLower C u p)) := by
  have hbneg : ∀ q∈C, |-u q|≤M := fun q hq => by simpa only [abs_neg] using hb q hq
  obtain ⟨q,hq,hqt,hval⟩ := perron_upper_recovery hbneg hp
  refine ⟨q,hq,hqt,?_⟩
  simpa only [perronLower,neg_neg] using hval.neg

theorem perron_upper_le_continuous {n : ℕ} {C : Set (Point n)} {u h : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) (hh : ContinuousOn h C) (hle : ∀ q∈C, u q≤h q)
    {p : Point n} (hp : p∈C) : perronUpper C u p≤h p := by
  apply le_of_forall_pos_le_add
  intro eps heps
  obtain ⟨rho,hrho,hmod⟩ := Metric.continuousWithinAt_iff.mp (hh p hp) eps heps
  have hr0 : Tendsto (fun k : ℕ => ((k:ℝ)+1)⁻¹) atTop (𝓝 0) := by
    simpa only [one_div] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hev : ∀ᶠ k : ℕ in atTop, ((k:ℝ)+1)⁻¹<rho := hr0 (eventually_lt_nhds hrho)
  obtain ⟨k,hk⟩ := hev.exists
  apply (perron_upper_le_local hb hp k).trans
  apply csSup_le (perron_localUpper_nonempty hp k)
  rintro r ⟨q,hq,rfl⟩
  have hm := hmod hq.1 ((Metric.mem_ball.mp hq.2).trans hk)
  have hm' : |h q-h p|<eps := by simpa only [Real.dist_eq] using hm
  exact (hle q hq.1).trans (by linarith [(abs_lt.mp hm').2])

theorem perron_continuous_le_lower {n : ℕ} {C : Set (Point n)} {u h : Point n → ℝ} {M : ℝ}
    (hb : ∀ q∈C, |u q|≤M) (hh : ContinuousOn h C) (hle : ∀ q∈C, h q≤u q)
    {p : Point n} (hp : p∈C) : h p≤perronLower C u p := by
  have hbneg : ∀ q∈C, |-u q|≤M := fun q hq => by simpa only [abs_neg] using hb q hq
  have hdom : ∀ q∈C, -u q≤-h q := fun q hq => neg_le_neg (hle q hq)
  have hl := perron_upper_le_continuous hbneg hh.neg hdom hp
  change perronUpper C (fun q => -u q) p≤-h p at hl
  dsimp only [perronLower]
  linarith

theorem perron_familySup_bounds {n : ℕ} {C : Set (Point n)} {S : Set (Point n → ℝ)}
    (hne : S.Nonempty) {M : ℝ} (hb : ∀ w∈S, ∀ p∈C, |w p|≤M)
    {p : Point n} (hp : p∈C) : |perronFamilySup S p|≤M := by
  obtain ⟨w,hw⟩ := hne
  have hnon : ({r | ∃ w∈S, r=w p} : Set ℝ).Nonempty := ⟨w p,w,hw,rfl⟩
  have hbd : BddAbove {r | ∃ w∈S, r=w p} := by
    refine ⟨M,?_⟩
    rintro r ⟨v,hv,rfl⟩
    exact (abs_le.mp (hb v hv p hp)).2
  apply abs_le.mpr
  constructor
  · exact (abs_le.mp (hb w hw p hp)).1.trans (le_csSup hbd ⟨w,hw,rfl⟩)
  · apply csSup_le hnon
    rintro r ⟨v,hv,rfl⟩
    exact (abs_le.mp (hb v hv p hp)).2

theorem perron_member_le_familySup {n : ℕ} {C : Set (Point n)} {S : Set (Point n → ℝ)}
    {M : ℝ} (hb : ∀ w∈S, ∀ p∈C, |w p|≤M)
    {w : Point n → ℝ} (hw : w∈S) {p : Point n} (hp : p∈C) : w p≤perronFamilySup S p := by
  have hbd : BddAbove {r | ∃ w∈S, r=w p} := by
    refine ⟨M,?_⟩
    rintro r ⟨v,hv,rfl⟩
    exact (abs_le.mp (hb v hv p hp)).2
  exact le_csSup hbd ⟨w,hw,rfl⟩

theorem perron_familySup_approx {n : ℕ} {S : Set (Point n → ℝ)} (hne : S.Nonempty)
    (p : Point n) {eps : ℝ} (heps : 0<eps) :
    ∃ w∈S, perronFamilySup S p-eps<w p := by
  obtain ⟨w,hw⟩ := hne
  have hnon : ({r | ∃ w∈S, r=w p} : Set ℝ).Nonempty := ⟨w p,w,hw,rfl⟩
  obtain ⟨r,⟨v,hv,rfl⟩,hr⟩ := exists_lt_of_lt_csSup hnon
    (show perronFamilySup S p-eps<perronFamilySup S p by linarith)
  exact ⟨v,hv,hr⟩

end Yau.LeafProofs.L05Aux
