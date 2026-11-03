import Yau.LeafProofs.L05PucciHarnackIntervalCover

open Filter MeasureTheory Set
open scoped Topology
noncomputable section
set_option maxHeartbeats 2000000
set_option backward.isDefEq.respectTransparency.types false
namespace Yau.LeafProofs.L05Aux
open Yau.Parabolic

theorem harnack_countable_forward_interval_measure {ι : Type*} [Countable ι] {m : ℝ} (hm : 0 < m)
    (p : ι → Prop) (a b : ι → ℝ) (hab : ∀ i, a i < b i) :
    (volume : Measure ℝ) (⋃ i, ⋃ (_ : p i), Ioc (a i) (b i)) ≤
      ENNReal.ofReal (1+1/m)*(volume : Measure ℝ)
        (⋃ i, ⋃ (_ : p i), Ioc (b i) (b i+m*(b i-a i))) := by
  classical
  let E : Finset ι → Set ℝ := fun s => ⋃ i∈s.filter p, Ioc (a i) (b i)
  have hMono : Monotone E := by
    intro s t hst x hx
    obtain ⟨i,hi,hIt⟩ := mem_iUnion₂.mp hx
    have hMember := Finset.mem_filter.mp hi
    exact mem_iUnion₂.mpr ⟨i,Finset.mem_filter.mpr ⟨hst hMember.1,hMember.2⟩,hIt⟩
  have hUnion : (⋃ s, E s)=⋃ i, ⋃ (_ : p i), Ioc (a i) (b i) := by
    ext t
    simp only [E,mem_iUnion]
    constructor
    · rintro ⟨s,i,hi,hIt⟩
      exact ⟨i,(Finset.mem_filter.mp hi).2,hIt⟩
    · rintro ⟨i,hp,hIt⟩
      exact ⟨{i},i,by simp only [Finset.mem_filter,Finset.mem_singleton]; exact ⟨trivial,hp⟩,hIt⟩
  rw [← hUnion,hMono.measure_iUnion]
  apply iSup_le
  intro s
  have hFinite := harnack_forward_interval_measure_finset hm (s.filter p) a b (fun i _ => hab i)
  have hSubset : (⋃ i∈s.filter p, Ioc (b i) (b i+m*(b i-a i))) ⊆
      (⋃ i, ⋃ (_ : p i), Ioc (b i) (b i+m*(b i-a i))) := by
    intro t ht
    obtain ⟨i,hi,hIt⟩ := mem_iUnion₂.mp ht
    exact mem_iUnion₂.mpr ⟨i,(Finset.mem_filter.mp hi).2,hIt⟩
  exact hFinite.trans (mul_le_mul_of_nonneg_left (measure_mono hSubset) zero_le)



theorem harnack_countable_forward_stack_measure
    {ι : Type*} [Countable ι] {n : ℕ} {m : ℝ} (hm : 0 < m)
    (S : ι → Set (Space n)) (a b : ι → ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hab : ∀ i, a i < b i) :
    (volume : Measure (Point n)) (⋃ i, S i ×ˢ Ioc (a i) (b i)) ≤
      ENNReal.ofReal (1+1/m)*(volume : Measure (Point n))
        (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))) := by
  have hE : MeasurableSet (⋃ i, S i ×ˢ Ioc (a i) (b i)) :=
    MeasurableSet.iUnion (fun i => (hS i).prod measurableSet_Ioc)
  have hF : MeasurableSet (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))) :=
    MeasurableSet.iUnion (fun i => (hS i).prod measurableSet_Ioc)
  have hSlice (x : Space n) :
      Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (a i) (b i))=
        ⋃ i, ⋃ (_ : x∈S i), Ioc (a i) (b i) := by
    ext t
    simp only [mem_preimage,mem_iUnion,mem_prod]
    aesop
  have hForwardSlice (x : Space n) :
      Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i)))=
        ⋃ i, ⋃ (_ : x∈S i), Ioc (b i) (b i+m*(b i-a i)) := by
    ext t
    simp only [mem_preimage,mem_iUnion,mem_prod]
    aesop
  rw [Measure.volume_eq_prod,Measure.prod_apply hE,Measure.prod_apply hF]
  calc
    _ ≤ ∫⁻ x : Space n, ENNReal.ofReal (1+1/m)*(volume : Measure ℝ)
        (Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i)))) := by
      apply lintegral_mono
      intro x
      change (volume : Measure ℝ) (Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (a i) (b i))) ≤
        ENNReal.ofReal (1+1/m)*(volume : Measure ℝ)
          (Prod.mk x ⁻¹' (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))))
      rw [hSlice,hForwardSlice]
      exact harnack_countable_forward_interval_measure hm (fun i => x∈S i) a b hab
    _ = _ := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top

theorem harnack_countable_parent_stack_measure_transfer
    {ι : Type*} [Countable ι] {n : ℕ} {m q : ℝ} (hm : 0 < m) (hq : 0 ≤ q)
    (S : ι → Set (Space n)) (a b : ι → ℝ)
    (hS : ∀ i, MeasurableSet (S i)) (hab : ∀ i, a i < b i)
    {A B : Set (Point n)} (hA : MeasurableSet A)
    (hPair : Pairwise (fun i j => Disjoint (S i ×ˢ Ioc (a i) (b i)) (S j ×ˢ Ioc (a j) (b j))))
    (hCover : A ⊆ ⋃ i, S i ×ˢ Ioc (a i) (b i))
    (hDensity : ∀ i, (volume : Measure (Point n)) (A ∩ (S i ×ˢ Ioc (a i) (b i))) ≤
      ENNReal.ofReal q*(volume : Measure (Point n)) (S i ×ˢ Ioc (a i) (b i)))
    (hForward : (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))) ⊆ B) :
    (volume : Measure (Point n)) A ≤ ENNReal.ofReal (q*(1+1/m))*(volume : Measure (Point n)) B := by
  let P := fun i => S i ×ˢ Ioc (a i) (b i)
  have hPMeas (i : ι) : MeasurableSet (P i) := (hS i).prod measurableSet_Ioc
  have hPairInter : Pairwise (fun i j => Disjoint (A ∩ P i) (A ∩ P j)) :=
    fun i j hij => (hPair hij).mono inter_subset_right inter_subset_right
  have hAeq : (⋃ i, A ∩ P i)=A := by
    ext p
    constructor
    · intro hp
      obtain ⟨i,hp⟩ := mem_iUnion.mp hp
      exact hp.1
    · intro hp
      obtain ⟨i,hi⟩ := mem_iUnion.mp (hCover hp)
      exact mem_iUnion.mpr ⟨i,hp,hi⟩
  have hMeasureA : (volume : Measure (Point n)) A=
      ∑' i, (volume : Measure (Point n)) (A ∩ P i) := by
    conv_lhs => rw [← hAeq]
    exact measure_iUnion hPairInter (fun i => hA.inter (hPMeas i))
  have hMeasureP : (volume : Measure (Point n)) (⋃ i, P i)=
      ∑' i, (volume : Measure (Point n)) (P i) := measure_iUnion hPair hPMeas
  have hStack := harnack_countable_forward_stack_measure hm S a b hS hab
  have hSub : (volume : Measure (Point n)) (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i))) ≤
      (volume : Measure (Point n)) B := measure_mono hForward
  calc
    _ = ∑' i, (volume : Measure (Point n)) (A ∩ P i) := hMeasureA
    _ ≤ ∑' i, ENNReal.ofReal q*(volume : Measure (Point n)) (P i) := ENNReal.tsum_le_tsum hDensity
    _ = ENNReal.ofReal q*(volume : Measure (Point n)) (⋃ i, P i) := by
      rw [ENNReal.tsum_mul_left,hMeasureP]
    _ ≤ ENNReal.ofReal q*(ENNReal.ofReal (1+1/m)*
        (volume : Measure (Point n)) (⋃ i, S i ×ˢ Ioc (b i) (b i+m*(b i-a i)))) :=
      mul_le_mul_of_nonneg_left hStack zero_le
    _ ≤ ENNReal.ofReal q*(ENNReal.ofReal (1+1/m)*(volume : Measure (Point n)) B) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hSub zero_le) zero_le
    _ = _ := by rw [← mul_assoc,← ENNReal.ofReal_mul hq]

end Yau.LeafProofs.L05Aux
