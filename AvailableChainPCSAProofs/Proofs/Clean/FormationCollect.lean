module
public import AvailableChainPCSAProofs.Proofs.Foundations.Install
public import AvailableChainPCSAProofs.Proofs.Foundations.AckPool
public import AvailableChainPCSA.Model.Frame
public import AvailableChainPCSA.Statements.Invariants
public import AvailableChainPCSAProofs.Proofs.Clean.FormationRelay

public section

/-! Formation PC collection (pcsa34-r4.3b §5.3).
These helpers use candidate and first-root resolution conditions.
FormationCollected has a different statement from Shared CollectClosed.
Shared RelayRun supplies installation carriage and PC acceptance origins.
No whole claim is exported. -/

open AvailableChain
namespace AvailableChain.PCSA
variable {n : Nat}

def FormationPCIdentity (st : State n) (s : Slot) (b : Block) : Prop :=
  ∃ C ∈ st.pcs, C.slot = s ∧ C.target = b

theorem FormationPCIdentity_def (st : State n) (s : Slot) (b : Block) :
    FormationPCIdentity st s b = (∃ C ∈ st.pcs, C.slot = s ∧ C.target = b) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

private theorem formation_identity_mono (st st' : State n) (s : Slot) (b : Block)
    (h : st.pcs ⊆ st'.pcs) : FormationPCIdentity st s b → FormationPCIdentity st' s b := by
  rintro ⟨C, hC, hs, hb⟩
  exact ⟨C, h hC, hs, hb⟩

private theorem formation_collect_step_frame (st : State n) (sr : Slot × BlockId) :
    let dst := match st.base.blocks.find? (fun b => b.root == sr.2) with
      | none => st
      | some b => match assemblePC st sr.1 b with
        | none => st
        | some C => installPC st C
    dst.base.blocks = st.base.blocks ∧ dst.ackPool = st.ackPool ∧
      dst.fg = st.fg ∧ st.pcs ⊆ dst.pcs := by
  dsimp only
  cases st.base.blocks.find? (fun b => b.root == sr.2) with
  | none => exact ⟨rfl, rfl, rfl, List.Subset.refl _⟩
  | some b =>
    dsimp only
    cases assemblePC st sr.1 b with
    | none => exact ⟨rfl, rfl, rfl, List.Subset.refl _⟩
    | some C => exact ⟨(installPC_frame st C).2.1,
        (installPC_frame st C).2.2.1, (installPC_frame st C).2.2.2.2,
        installPC_pcs_mono st C⟩

private theorem formation_identity_install (st : State n) (C : PC n) :
    FormationPCIdentity (installPC st C) C.slot C.target := by
  cases h : st.pcs.any (fun A => A.slot == C.slot && A.target == C.target) with
  | true =>
    rw [installPC_duplicate st C h]
    obtain ⟨A, ha, he⟩ := List.any_eq_true.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at he
    exact ⟨A, ha, he⟩
  | false =>
    refine ⟨C, ?_, rfl, rfl⟩
    rw [installPC_pcs_new st C h]
    exact List.mem_append_right _ (List.mem_singleton_self _)

private theorem formation_collect_fold_mono (cs : List (Slot × BlockId)) (st : State n) :
    st.pcs ⊆ (cs.foldl (fun acc sr =>
      match acc.base.blocks.find? (fun b => b.root == sr.2) with
      | none => acc
      | some b => match assemblePC acc sr.1 b with
        | none => acc
        | some C => installPC acc C) st).pcs := by
  induction cs generalizing st with
  | nil => exact List.Subset.refl _
  | cons sr cs ih =>
    rw [List.foldl_cons]
    exact List.Subset.trans (formation_collect_step_frame st sr).2.2.2 (ih _)

private theorem formation_assemble_eq_of_frame (st st' : State n) (s : Slot) (b : Block)
    (hb : st'.base.blocks = st.base.blocks) (ha : st'.ackPool = st.ackPool)
    (hf : st'.fg = st.fg) : assemblePC st' s b = assemblePC st s b := by
  delta assemblePC pcValid acksOn activeCompatible
  rw [hb, ha, hf]

private theorem formation_collect_fold_identity (cs : List (Slot × BlockId))
    (st : State n) (s : Slot) (b : Block) (C : PC n)
    (hm : (s, b.root) ∈ cs)
    (hb : st.base.blocks.find? (fun B => B.root == b.root) = some b)
    (hc : assemblePC st s b = some C) :
    FormationPCIdentity (cs.foldl (fun acc sr =>
      match acc.base.blocks.find? (fun B => B.root == sr.2) with
      | none => acc
      | some B => match assemblePC acc sr.1 B with
        | none => acc
        | some D => installPC acc D) st) s b := by
  induction cs generalizing st with
  | nil => exact (List.not_mem_nil hm).elim
  | cons sr cs ih =>
    rw [List.foldl_cons]
    let dst := match st.base.blocks.find? (fun B => B.root == sr.2) with
      | none => st
      | some B => match assemblePC st sr.1 B with
        | none => st
        | some D => installPC st D
    have hd := formation_collect_step_frame st sr
    rcases List.mem_cons.mp hm with he | hm
    · subst sr
      change FormationPCIdentity (cs.foldl _ dst) s b
      apply formation_identity_mono dst _ s b (formation_collect_fold_mono cs dst)
      dsimp only [dst]
      rw [hb]
      dsimp only
      rw [hc]
      have he := (assemblePC_some_iff st s b C).mp hc
      obtain rfl := he.1
      exact formation_identity_install st _
    · apply ih dst hm
      · rw [hd.1]
        exact hb
      · rw [formation_assemble_eq_of_frame st dst s b hd.1 hd.2.1 hd.2.2.1]
        exact hc

/-- A visited, resolved candidate is installed by collection. -/
theorem pcsa_formation_collect_identity (st : State n) (s : Slot) (b : Block)
    (C : PC n)
    (hm : (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
      (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups)
    (hb : st.base.blocks.find? (fun B => B.root == b.root) = some b)
    (hc : assemblePC st s b = some C) : FormationPCIdentity (collectPCs st) s b := by
  delta collectPCs
  exact formation_collect_fold_identity _ st s b C hm hb hc

private theorem formation_collect_new_origin (cs : List (Slot × BlockId))
    (st : State n) (C : PC n)
    (hm : C ∈ (cs.foldl (fun acc sr =>
      match acc.base.blocks.find? (fun B => B.root == sr.2) with
      | none => acc
      | some B => match assemblePC acc sr.1 B with
        | none => acc
        | some D => installPC acc D) st).pcs)
    (hNew : C ∉ st.pcs) :
    (C.slot, C.target.root) ∈ cs ∧
      st.base.blocks.find? (fun B => B.root == C.target.root) = some C.target ∧
      assemblePC st C.slot C.target = some C := by
  induction cs generalizing st with
  | nil => exact (hNew hm).elim
  | cons sr cs ih =>
    rw [List.foldl_cons] at hm
    let dst := match st.base.blocks.find? (fun B => B.root == sr.2) with
      | none => st
      | some B => match assemblePC st sr.1 B with
        | none => st
        | some D => installPC st D
    have hf := formation_collect_step_frame st sr
    by_cases hDst : C ∈ dst.pcs
    · dsimp only [dst] at hDst
      cases hb : st.base.blocks.find? (fun B => B.root == sr.2) with
      | none => rw [hb] at hDst; exact (hNew hDst).elim
      | some B =>
        rw [hb] at hDst
        dsimp only at hDst
        cases hc : assemblePC st sr.1 B with
        | none => rw [hc] at hDst; exact (hNew hDst).elim
        | some D =>
          rw [hc] at hDst
          obtain hOld | rfl := mem_installPC_pcs st D C hDst
          · exact (hNew hOld).elim
          · have he := (assemblePC_some_iff st sr.1 B C).mp hc
            have hs : C.slot = sr.1 := congrArg PC.slot he.1
            have ht : C.target = B := congrArg PC.target he.1
            have hr : B.root = sr.2 := by simpa only [beq_iff_eq] using List.find?_some hb
            have hp : (C.slot, C.target.root) = sr := by
              apply Prod.ext
              · exact hs
              · exact (congrArg Block.root ht).trans hr
            refine ⟨hp.symm ▸ (List.mem_cons_self : sr ∈ sr :: cs), ?_, ?_⟩
            · rw [ht, hr]
              exact hb
            · rw [hs, ht]
              exact hc
    · obtain ⟨hcs, hb, hc⟩ := ih dst hm hDst
      refine ⟨List.mem_cons_of_mem sr hcs, ?_, ?_⟩
      · rw [hf.1] at hb
        exact hb
      · rw [formation_assemble_eq_of_frame st dst C.slot C.target hf.1 hf.2.1 hf.2.2.1] at hc
        exact hc

/-- A new collected certificate is exactly a resolved assembly candidate. -/
theorem pcsa_formation_collect_new_origin (st : State n) (C : PC n)
    (hm : C ∈ (collectPCs st).pcs) (hNew : C ∉ st.pcs) :
    (C.slot, C.target.root) ∈ (st.ackPool.filterMap (fun a =>
      (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups ∧
      st.base.blocks.find? (fun B => B.root == C.target.root) = some C.target ∧
      assemblePC st C.slot C.target = some C := by
  delta collectPCs at hm
  exact formation_collect_new_origin _ st C hm hNew

/-- Every supported root candidate has its installed PC identity. -/
def FormationCollected (st : State n) : Prop :=
  ∀ (s : Slot) (b : Block) (C : PC n),
    (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
      (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups →
    st.base.blocks.find? (fun B => B.root == b.root) = some b →
    assemblePC st s b = some C → FormationPCIdentity st s b

theorem FormationCollected_def (st : State n) : FormationCollected st =
    (∀ (s : Slot) (b : Block) (C : PC n),
      (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
        (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups →
      st.base.blocks.find? (fun B => B.root == b.root) = some b →
      assemblePC st s b = some C → FormationPCIdentity st s b) := by
  apply propext
  exact ⟨fun h => h, fun h => h⟩

/-- Collection leaves no supported candidate without an installed identity. -/
theorem pcsa_formation_collect_invariant (st : State n) : FormationCollected (collectPCs st) := by
  intro s b C hm hb hc
  have hf := collectPCs_frame st
  rw [hf.2.2.1] at hm
  rw [hf.2.1] at hb
  rw [formation_assemble_eq_of_frame st (collectPCs st) s b
    hf.2.1 hf.2.2.1 hf.2.2.2.2] at hc
  exact pcsa_formation_collect_identity st s b C hm hb hc

/-- Changes outside the assembly inputs preserve collection closure. -/
theorem pcsa_formation_collected_of_frame (st st' : State n)
    (h : FormationCollected st)
    (hb : st'.base.blocks = st.base.blocks) (ha : st'.ackPool = st.ackPool)
    (hf : st'.fg = st.fg) (hp : st.pcs ⊆ st'.pcs) : FormationCollected st' := by
  intro s b C hm hfind hc
  rw [ha] at hm
  rw [hb] at hfind
  rw [formation_assemble_eq_of_frame st st' s b hb ha hf] at hc
  exact formation_identity_mono st st' s b hp (h s b C hm hfind hc)

private theorem formation_pc_nonempty (C : PC n) (hn : 0 < n)
    (hw : C.wellFormed = true) : C.acks ≠ [] := by
  have h1 := (Bool.and_eq_true_iff.mp hw).1
  have h2 := (Bool.and_eq_true_iff.mp h1).1
  have hCard : pcQuorum n ≤ C.acks.length :=
    of_decide_eq_true (Bool.and_eq_true_iff.mp h2).2
  have hq : 0 < pcQuorum n := by delta pcQuorum; omega
  intro he
  rw [he] at hCard
  simp only [List.length_nil] at hCard
  omega

private theorem formation_firstPerSeat_subset (as : List (AckWire n)) :
    firstPerSeat as ⊆ as := by
  delta firstPerSeat
  suffices ∀ acc : List (AckWire n), acc ⊆ as →
      (as.foldl (fun acc a =>
        if acc.any (fun old => old.seat? == a.seat?) then acc else acc ++ [a]) acc) ⊆ as
    from this [] (by simp)
  intro acc h
  apply List.foldlRecOn (motive := fun acc => acc ⊆ as)
  · exact h
  · intro acc ha a hm
    split
    · exact ha
    · intro b hb
      rcases List.mem_append.mp hb with hb | hb
      · exact ha hb
      · exact List.mem_singleton.mp hb ▸ hm

private theorem formation_assembly_candidate (st : State n) (s : Slot) (b : Block)
    (C : PC n) (hn : 0 < n) (hc : assemblePC st s b = some C) :
    (s, b.root) ∈ (st.ackPool.filterMap (fun a =>
      (AckWire.decode? a).map (fun x => (x.1, x.2.2)))).eraseDups := by
  have he := (assemblePC_some_iff st s b C).mp hc
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp he.2).1).1
  obtain ⟨a, ha⟩ := List.exists_mem_of_ne_nil C.acks (formation_pc_nonempty C hn hw)
  have hm : a ∈ acksOn st s b.root := by
    rw [he.1] at ha
    exact formation_firstPerSeat_subset _ ha
  obtain ⟨hp, i, hd⟩ := (mem_acksOn_iff st s b.root a).mp hm
  apply List.mem_eraseDups.mpr
  exact List.mem_filterMap.mpr ⟨a, hp, by rw [hd]; rfl⟩

/-- A resolved assembly has its installed identity in a collected store. -/
theorem pcsa_formation_collected_identity (st : State n) (s : Slot) (b : Block)
    (C : PC n) (hn : 0 < n) (h : FormationCollected st)
    (hb : st.base.blocks.find? (fun B => B.root == b.root) = some b)
    (hc : assemblePC st s b = some C) : FormationPCIdentity st s b :=
  h s b C (formation_assembly_candidate st s b C hn hc) hb hc

private theorem formation_assemble_eq_of_on (st st' : State n) (s : Slot) (b : Block)
    (hb : st'.base.blocks = st.base.blocks) (hf : st'.fg = st.fg)
    (ha : acksOn st' s b.root = acksOn st s b.root) :
    assemblePC st' s b = assemblePC st s b := by
  delta assemblePC
  rw [ha]
  delta pcValid activeCompatible
  rw [hb, hf]

private theorem formation_poolRaw_on_miss (st : State n) (a : AckWire n)
    (s : Slot) (r : BlockId) (hMiss : ∀ i, (AckWire.decode? a) ≠ some (s, i, r)) :
    acksOn (poolAckRaw st a) s r = acksOn st s r := by
  delta poolAckRaw
  cases hd : (AckWire.decode? a) with
  | none => rfl
  | some x =>
    dsimp only
    split
    · rfl
    · delta acksOn
      rw [List.filter_append]
      have hm : (match (AckWire.decode? a) with
          | some (s', _, r') => s' == s && r' == r
          | none => false) = false := by
        rw [hd]
        rcases x with ⟨s', i, r'⟩
        dsimp only
        apply Bool.eq_false_iff.mpr
        intro ht
        simp only [Bool.and_eq_true, beq_iff_eq] at ht
        obtain ⟨rfl, rfl⟩ := ht
        exact hMiss i hd
      have hnil : [a].filter (fun a => match (AckWire.decode? a) with
          | some (s', _, r') => s' == s && r' == r
          | none => false) = [] := by
        apply List.filter_eq_nil_iff.mpr
        intro b hb
        obtain rfl := List.mem_singleton.mp hb
        intro ht
        have hh := hm.symm.trans ht
        cases hh
      exact (congrArg (fun xs => st.ackPool.filter (fun a => match (AckWire.decode? a) with
        | some (s', _, r') => s' == s && r' == r
        | none => false) ++ xs) hnil).trans (List.append_nil _)

private theorem formation_raw_on_miss (st : State n) (as : List (AckWire n))
    (s : Slot) (r : BlockId) (hMiss : ∀ a ∈ as, ∀ i, (AckWire.decode? a) ≠ some (s, i, r)) :
    acksOn (as.foldl poolAckRaw st) s r = acksOn st s r := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih =>
    rw [List.foldl_cons, ih _ (fun b hb => hMiss b (List.mem_cons_of_mem a hb)),
      formation_poolRaw_on_miss st a s r (hMiss a List.mem_cons_self)]

private theorem formation_raw_frame (st : State n) (as : List (AckWire n)) :
    (as.foldl poolAckRaw st).base.blocks = st.base.blocks ∧
      (as.foldl poolAckRaw st).fg = st.fg ∧ (as.foldl poolAckRaw st).pcs = st.pcs := by
  induction as generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons a as ih =>
    rw [List.foldl_cons]
    have ht := ih (poolAckRaw st a)
    have hs := poolAckRaw_frame st a
    exact ⟨ht.1.trans (congrArg (fun v => v.blocks) hs.2.2.1),
      ht.2.1.trans hs.2.2.2, ht.2.2.trans hs.1⟩

private theorem formation_pc_ack_decode (D : PC n) (hD : D.wellFormed = true)
    (a : AckWire n) (ha : a ∈ D.acks) :
    ∃ i, (AckWire.decode? a) = some (D.slot, i, D.target.root) := by
  have hd := List.all_eq_true.mp (Bool.and_eq_true_iff.mp hD).2 a ha
  rcases a with ⟨auth, root⟩
  cases auth with
  | none => change false = true at hd; cases hd
  | proposer k => change false = true at hd; cases hd
  | seat l j =>
    cases l with
    | head k => change false = true at hd; cases hd
    | fg => change false = true at hd; cases hd
    | ack k =>
      change (k == D.slot && root == D.target.root) = true at hd
      simp only [Bool.and_eq_true, beq_iff_eq] at hd
      obtain ⟨rfl, rfl⟩ := hd
      exact ⟨j, rfl⟩

/-- A standalone PC wire can newly install only its slot and root.
Collection closure excludes an unrelated candidate from an earlier pool. -/
theorem pcsa_formation_admitPC_root (st : State n) (D C : PC n) (hn : 0 < n)
    (hClosed : FormationCollected st) (hD : D.wellFormed = true)
    (hNew : ¬FormationPCIdentity st C.slot C.target)
    (hm : C ∈ (admitPC st D).pcs) : D.slot = C.slot ∧ D.target.root = C.target.root := by
  have hf := formation_raw_frame st D.acks
  have hNot : C ∉ (D.acks.foldl poolAckRaw st).pcs := by
    rw [hf.2.2]
    intro hc
    exact hNew ⟨C, hc, rfl, rfl⟩
  change C ∈ (if D.wellFormed then collectPCs (D.acks.foldl poolAckRaw st) else st).pcs at hm
  rw [ite_eq_left hD] at hm
  obtain ⟨_, hb, hc⟩ := pcsa_formation_collect_new_origin _ C hm hNot
  by_contra hDiff
  have hMiss : ∀ a ∈ D.acks, ∀ i, (AckWire.decode? a) ≠ some (C.slot, i, C.target.root) := by
    intro a ha i hi
    obtain ⟨j, hd⟩ := formation_pc_ack_decode D hD a ha
    have he := Option.some.inj (hd.symm.trans hi)
    simp only [Prod.mk.injEq] at he
    exact hDiff ⟨he.1, he.2.2⟩
  have hOn := formation_raw_on_miss st D.acks C.slot C.target.root hMiss
  rw [formation_assemble_eq_of_on st _ C.slot C.target hf.1 hf.2.1 hOn] at hc
  rw [hf.1] at hb
  exact hNew (pcsa_formation_collected_identity st _ _ C hn hClosed hb hc)

private theorem formation_ack_shape (a : AckWire n) (s : Slot) (i : Fin n)
    (r : BlockId) (hd : (AckWire.decode? a) = some (s, i, r)) :
    a = ⟨.seat (.ack s) i, r⟩ := by
  rcases a with ⟨auth, root⟩
  cases auth with
  | none => cases hd
  | proposer k => cases hd
  | seat l j =>
    cases l with
    | head k => cases hd
    | fg => cases hd
    | ack k =>
      change some (k, j, root) = some (s, i, r) at hd
      simp only [Option.some.injEq, Prod.mk.injEq] at hd
      obtain ⟨rfl, rfl, rfl⟩ := hd
      rfl

private theorem formation_first_fold_covers (D : List (AckWire n))
    (hInj : ∀ x ∈ D, ∀ y ∈ D, (AckWire.seat? x) = (AckWire.seat? y) → x = y)
    (as acc : List (AckWire n)) (hAs : as ⊆ D) (hAcc : acc ⊆ D)
    (a : AckWire n) (ha : a ∈ acc ∨ a ∈ as) :
    a ∈ as.foldl (fun acc b =>
      if acc.any (fun old => (AckWire.seat? old) == (AckWire.seat? b)) then acc
      else acc ++ [b]) acc := by
  induction as generalizing acc with
  | nil => simpa using ha
  | cons b as ih =>
    rw [List.foldl_cons]
    let next :=
      if acc.any (fun old => (AckWire.seat? old) == (AckWire.seat? b)) then acc
      else acc ++ [b]
    have hb : b ∈ D := hAs List.mem_cons_self
    have hMono : acc ⊆ next := by
      dsimp only [next]
      split
      · exact List.Subset.refl _
      · exact List.subset_append_left _ _
    have hB : b ∈ next := by
      dsimp only [next]
      split
      · rename_i hh
        obtain ⟨x, hx, he⟩ := List.any_eq_true.mp hh
        have hxb := hInj x (hAcc hx) b hb (beq_iff_eq.mp he)
        exact hxb ▸ hx
      · exact List.mem_append_right _ (List.mem_singleton_self _)
    have hNext : next ⊆ D := by
      dsimp only [next]
      split
      · exact hAcc
      · intro x hx
        rcases List.mem_append.mp hx with hx | hx
        · exact hAcc hx
        · exact List.mem_singleton.mp hx ▸ hb
    apply ih next (fun x hx => hAs (List.mem_cons_of_mem b hx)) hNext
    rcases ha with ha | ha
    · exact Or.inl (hMono ha)
    · rcases List.mem_cons.mp ha with rfl | ha
      · exact Or.inl hB
      · exact Or.inr ha

/-- In a single slot/root pool, first-per-seat selection drops only duplicates. -/
theorem pcsa_formation_firstPerSeat_covers (as : List (AckWire n)) (s : Slot)
    (r : BlockId) (hUniform : ∀ a ∈ as, ∃ i, (AckWire.decode? a) = some (s, i, r)) :
    as ⊆ firstPerSeat as := by
  intro a ha
  delta firstPerSeat
  apply formation_first_fold_covers as ?_ as [] (List.Subset.refl _) (by simp) a (Or.inr ha)
  intro x hx y hy he
  obtain ⟨i, hd⟩ := hUniform x hx
  obtain ⟨j, hu⟩ := hUniform y hy
  change (AckWire.decode? x).map (fun z => z.2.1) = (AckWire.decode? y).map (fun z => z.2.1) at he
  rw [hd, hu] at he
  have hij : i = j := Option.some.inj he
  subst j
  exact (formation_ack_shape x s i r hd).trans (formation_ack_shape y s i r hu).symm

private theorem formation_poolAck_cases (p : Params) (st : State p.n) (a : AckWire p.n) :
    poolAck p st a = st ∨ poolAck p st a = { st with ackPool := st.ackPool ++ [a] } := by
  delta poolAck
  cases (AckWire.decode? a) with
  | none => exact Or.inl rfl
  | some x =>
    rcases x with ⟨s, i, r⟩
    dsimp only
    split
    · exact Or.inl rfl
    · split
      · exact Or.inl rfl
      · exact Or.inr rfl

private theorem formation_poolAck_frame (p : Params) (st : State p.n) (a : AckWire p.n) :
    (poolAck p st a).base.blocks = st.base.blocks ∧
      (poolAck p st a).fg = st.fg ∧ (poolAck p st a).pcs = st.pcs := by
  rcases formation_poolAck_cases p st a with he | he <;> rw [he]
  all_goals exact ⟨rfl, rfl, rfl⟩

private theorem formation_filter_append_missing {α : Type} (xs : List α) (a : α)
    (f : α → Bool) (hNot : a ∉ (xs ++ [a]).filter f) :
    (xs ++ [a]).filter f = xs.filter f := by
  have hMiss : f a = false := by
    apply Bool.eq_false_iff.mpr
    intro ht
    exact hNot (List.mem_filter.mpr
      ⟨List.mem_append_right _ (List.mem_singleton_self _), ht⟩)
  rw [List.filter_append]
  have hnil : [a].filter f = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro b hb
    obtain rfl := List.mem_singleton.mp hb
    intro ht
    have hh := hMiss.symm.trans ht
    cases hh
  exact (congrArg (fun ys => xs.filter f ++ ys) hnil).trans (List.append_nil _)

private theorem formation_poolAck_on_missing (p : Params) (st : State p.n)
    (a : AckWire p.n) (s : Slot) (r : BlockId)
    (hNot : a ∉ acksOn (poolAck p st a) s r) :
    acksOn (poolAck p st a) s r = acksOn st s r := by
  rcases formation_poolAck_cases p st a with he | he
  · rw [he]
  · rw [he] at hNot ⊢
    delta acksOn at hNot ⊢
    exact formation_filter_append_missing st.ackPool a _ hNot

/-- A completing ack belongs to the certificate that its call newly installs. -/
theorem pcsa_formation_admitAck_contains (p : Params) (st : State p.n)
    (a : AckWire p.n) (C : PC p.n) (hClosed : FormationCollected st)
    (hNew : ¬FormationPCIdentity st C.slot C.target)
    (hm : C ∈ (admitAck p st a).pcs) : a ∈ C.acks := by
  have hf := formation_poolAck_frame p st a
  have hNot : C ∉ (poolAck p st a).pcs := by
    rw [hf.2.2]
    intro hc
    exact hNew ⟨C, hc, rfl, rfl⟩
  obtain ⟨_, hb, hc⟩ := pcsa_formation_collect_new_origin _ C hm hNot
  by_contra hA
  have hMiss : a ∉ acksOn (poolAck p st a) C.slot C.target.root := by
    intro ha
    have hCover := pcsa_formation_firstPerSeat_covers
      (acksOn (poolAck p st a) C.slot C.target.root) C.slot C.target.root
      (fun b hb => (mem_acksOn_iff _ _ _ b).mp hb |>.2)
    have hIn := hCover ha
    have he := congrArg PC.acks ((assemblePC_some_iff _ _ _ C).mp hc).1
    change C.acks = firstPerSeat (acksOn (poolAck p st a) C.slot C.target.root) at he
    rw [← he] at hIn
    exact hA hIn
  have hOn := formation_poolAck_on_missing p st a C.slot C.target.root hMiss
  rw [formation_assemble_eq_of_on st _ C.slot C.target hf.1 hf.2.1 hOn] at hc
  rw [hf.1] at hb
  exact hNew (pcsa_formation_collected_identity st _ _ C p.nPos hClosed hb hc)

private theorem formation_accepted_base (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n))
    (hTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)
    (hParent : parentFG st N.erase = some P)
    (hAcc : blockAccepted p st s N P = true) :
    (GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks =
      st.base.blocks ++ [N.erase] := by
  have hLook := FGSA.pickPair_some_spec st.fg.TF _ hParent
  have hP : eraseFG P = N.erase.parent := of_decide_eq_true hLook.2
  have hf := hAcc
  change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
    !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
    SimplexFG.FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
    decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
    rowsValidForParent p P N.erase.slot N.rows && (N.pc.map PC.wellFormed).getD true &&
    namedContentOk p N) = true at hf
  simp only [Bool.and_eq_true, bne_iff_ne, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not, beq_iff_eq] at hf
  have hSlot : N.erase.slot ≤ st.slot p := by tauto
  have hFresh : ¬∃ B ∈ st.fg.TF, B.root = N.erase.root := hf.1.1.1.1.1.1.2
  have hPS : N.erase.parent.slot < N.erase.slot := by tauto
  have hS : s = N.erase.slot := by tauto
  have hNot : N.erase ∉ st.base.blocks := by
    intro hb
    obtain ⟨B, hB, he⟩ := (hTree _).mp hb
    apply hFresh
    exact ⟨B, hB, by rw [← he]; cases B <;> rfl⟩
  have hBase := FGSA.admitProposal_of_accept p.toParams.engine st.base s
    (.proposal N.erase (N.raw.map baseHead) (N.support.map baseHead)) N.erase
    (N.raw.map baseHead) hSlot ((hTree _).mpr ⟨P, hLook.1, hP⟩) hNot hPS hS
  have hBlocks := (FGSA.foldVotes_fields p.toParams.engine (N.raw.map baseHead)
    { st.base with
      blocks := st.base.blocks ++ [N.erase]
      blockStamp := st.base.blockStamp ++ [(N.erase, st.base.now)]
      proposals := st.base.proposals ++ [baseProposal s N.erase N.raw N.support] }).1
  exact (congrArg (fun v : GridCO.State p.n .root => v.blocks) hBase).trans hBlocks

private abbrev formationCollectWindow (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) : State p.n :=
  let st1 : State p.n := { st with
    base := GridCO.admitProposal p.toParams.engine st.base
      (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead) }
  let st1 := match N.pc with
    | none => st1
    | some D => if pcValid st1 D &&
        !st1.pcs.any (fun old => old.slot == D.slot && old.target == D.target)
      then deleteConflictingLeases st1 D else st1
  let st1 := { st1 with
    fg := FGSA.Window.on_block p p.K_W st1.fg (fgBlock P N.erase N.rows)
    proposals := st.proposals ++ [⟨.proposer s, .proposal N⟩] }
  st1

private abbrev formationCollectPre (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) : State p.n :=
  let updated := formationCollectWindow p st s N P
  if updated.fg.F = st.fg.F then updated else reconcile updated

private abbrev formationCollectInput (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) : State p.n :=
  N.pcAcks.foldl poolAckRaw (formationCollectPre p st s N P)

private theorem formation_normalize_blocks (st : State n) :
    (normalizeS st).base.blocks = st.base.blocks := by
  delta normalizeS
  split <;> rfl

private theorem formation_normalize_acks (st : State n) :
    (normalizeS st).ackPool = st.ackPool := by
  delta normalizeS
  split <;> rfl

private theorem formation_reconcile_blocks (st : State n) :
    (reconcile st).base.blocks = st.base.blocks := by
  delta reconcile
  rw [formation_normalize_blocks]

private theorem formation_reconcile_acks (st : State n) :
    (reconcile st).ackPool = st.ackPool := by
  delta reconcile
  rw [formation_normalize_acks]

private theorem formation_normalize_pcs (st : State n) :
    (normalizeS st).pcs = st.pcs := by
  delta normalizeS
  split <;> rfl

private theorem formation_reconcile_pcs_sub (st : State n) :
    (reconcile st).pcs ⊆ st.pcs := by
  intro C hC
  delta reconcile at hC
  rw [formation_normalize_pcs] at hC
  exact (List.mem_filter.mp hC).1

private theorem formation_if_reconcile_blocks (st : State n)
    (F : SimplexFG.FGBlock (Fin n)) :
    (if st.fg.F = F then st else reconcile st).base.blocks = st.base.blocks := by
  by_cases h : st.fg.F = F
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, formation_reconcile_blocks]

private theorem formation_if_reconcile_acks (st : State n)
    (F : SimplexFG.FGBlock (Fin n)) :
    (if st.fg.F = F then st else reconcile st).ackPool = st.ackPool := by
  by_cases h : st.fg.F = F
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, formation_reconcile_acks]

private theorem formation_if_reconcile_pcs_sub (st : State n)
    (F : SimplexFG.FGBlock (Fin n)) :
    (if st.fg.F = F then st else reconcile st).pcs ⊆ st.pcs := by
  by_cases h : st.fg.F = F
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    exact formation_reconcile_pcs_sub st

private theorem formation_window_blocks (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) :
    (formationCollectWindow p st s N P).base.blocks =
      (GridCO.admitProposal p.toParams.engine st.base
        (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks := by
  delta formationCollectWindow
  cases hp : N.pc with
  | none => rfl
  | some D =>
    dsimp only
    split <;> rfl

private theorem formation_window_acks (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) :
    (formationCollectWindow p st s N P).ackPool = st.ackPool := by
  delta formationCollectWindow
  cases hp : N.pc with
  | none => rfl
  | some D =>
    dsimp only
    split <;> rfl

private theorem formation_window_pcs (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) :
    (formationCollectWindow p st s N P).pcs = st.pcs := by
  delta formationCollectWindow
  cases hp : N.pc with
  | none => rfl
  | some D =>
    dsimp only
    split <;> rfl

private theorem formation_pre_blocks (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) :
    (formationCollectPre p st s N P).base.blocks =
      (GridCO.admitProposal p.toParams.engine st.base
        (baseProposal s N.erase N.raw N.support) N.erase (N.raw.map baseHead)).blocks := by
  exact (formation_if_reconcile_blocks (formationCollectWindow p st s N P) st.fg.F).trans
    (formation_window_blocks p st s N P)

private theorem formation_pre_acks (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) :
    (formationCollectPre p st s N P).ackPool = st.ackPool := by
  exact (formation_if_reconcile_acks (formationCollectWindow p st s N P) st.fg.F).trans
    (formation_window_acks p st s N P)

private theorem formation_pre_pcs_sub (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) :
    (formationCollectPre p st s N P).pcs ⊆ st.pcs := by
  have hsub := formation_if_reconcile_pcs_sub (formationCollectWindow p st s N P) st.fg.F
  rw [formation_window_pcs] at hsub
  exact hsub

private theorem formation_row_pcs (p : Params) (st : State p.n) (a : RowWire p.n) :
    (admitRow p st a).pcs = st.pcs := by
  delta admitRow
  cases hd : RowWire.decode? a with
  | none => rfl
  | some x =>
    dsimp only
    split <;> rfl

private theorem formation_rows_pcs (p : Params) (st : State p.n)
    (as : List (RowWire p.n)) : (as.foldl (admitRow p) st).pcs = st.pcs := by
  induction as generalizing st with
  | nil => rfl
  | cons a as ih => rw [List.foldl_cons, ih, formation_row_pcs]

private theorem formation_acksOn_of_pool_eq (st st' : State n) (s : Slot) (r : BlockId)
    (ha : st'.ackPool = st.ackPool) : acksOn st' s r = acksOn st s r := by
  delta acksOn
  rw [ha]

private theorem formation_input_on_miss (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) (C : PC p.n)
    (hWF : (N.pc.map PC.wellFormed).getD true = true)
    (hMiss : ∀ D ∈ N.pc, ¬(D.slot = C.slot ∧ D.target.root = C.target.root)) :
    acksOn (formationCollectInput p st s N P) C.slot C.target.root =
      acksOn st C.slot C.target.root := by
  apply Eq.trans ?_ (formation_acksOn_of_pool_eq st _ C.slot C.target.root
    (formation_pre_acks p st s N P))
  delta formationCollectInput
  apply formation_raw_on_miss
  intro a ha i hi
  change a ∈ (N.pc.map PC.acks).getD [] at ha
  cases hp : N.pc with
  | none => rw [hp] at ha; exact (List.not_mem_nil ha).elim
  | some D =>
    rw [hp] at ha hWF
    have hd : D.wellFormed = true := hWF
    obtain ⟨j, hj⟩ := formation_pc_ack_decode D hd a ha
    have he := Option.some.inj (hj.symm.trans hi)
    simp only [Prod.mk.injEq] at he
    exact hMiss D (by rw [hp]; exact Option.mem_def.mpr rfl) ⟨he.1, he.2.2⟩

private theorem formation_find_old_or_new (xs : List Block) (N b : Block)
    (hf : (xs ++ [N]).find? (fun B => B.root == b.root) = some b) :
    xs.find? (fun B => B.root == b.root) = some b ∨ b = N := by
  rw [List.find?_append] at hf
  cases ho : xs.find? (fun B => B.root == b.root) with
  | none =>
    rw [ho] at hf
    by_cases hroot : (N.root == b.root) = true
    · simp only [List.find?_cons, hroot] at hf
      exact Or.inr (Option.some.inj hf).symm
    · simp only [List.find?_cons, List.find?_nil, hroot] at hf
      cases hf
  | some B =>
    rw [ho] at hf
    obtain rfl := Option.some.inj hf
    exact Or.inl rfl

private theorem formation_pc_slot (C : PC n) (hw : C.wellFormed = true) :
    C.target.slot = C.slot := by
  have h1 := (Bool.and_eq_true_iff.mp hw).1
  have h2 := (Bool.and_eq_true_iff.mp h1).1
  have h3 := (Bool.and_eq_true_iff.mp h2).1
  exact beq_iff_eq.mp (Bool.and_eq_true_iff.mp h3).2

/-- An accepted proposal installs only its block slot/root or its carried PC slot/root. -/
private theorem pcsa_formation_accepted_proposal_root (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (P : SimplexFG.FGBlock (Fin p.n)) (C : PC p.n)
    (hTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)
    (hParent : parentFG st N.erase = some P) (hAcc : blockAccepted p st s N P = true)
    (hClosed : FormationCollected st) (hF : st.fg.F = .genesis)
    (hWF : (N.pc.map PC.wellFormed).getD true = true)
    (hNew : ¬FormationPCIdentity st C.slot C.target)
    (hm : C ∈ (N.rows.foldl (admitRow p)
      (collectPCs (formationCollectInput p st s N P))).pcs) :
    (C.slot = N.erase.slot ∧ C.target.root = N.erase.root) ∨
      ∃ D ∈ N.pc, D.slot = C.slot ∧ D.target.root = C.target.root := by
  rw [formation_rows_pcs] at hm
  have hInput : C ∉ (formationCollectInput p st s N P).pcs := by
    intro hC
    change C ∈ (N.pcAcks.foldl poolAckRaw (formationCollectPre p st s N P)).pcs at hC
    rw [(formation_raw_frame _ N.pcAcks).2.2] at hC
    exact hNew ⟨C, formation_pre_pcs_sub p st s N P hC, rfl, rfl⟩
  obtain ⟨_, hb, hc⟩ := pcsa_formation_collect_new_origin _ C hm hInput
  have hValid := pcsa_assemblePC_valid _ _ _ C hc
  have hw := (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hValid).1).1
  have hBlocks : (formationCollectInput p st s N P).base.blocks =
      st.base.blocks ++ [N.erase] := by
    exact (formation_raw_frame _ N.pcAcks).1.trans
      ((formation_pre_blocks p st s N P).trans
        (formation_accepted_base p st s N P hTree hParent hAcc))
  rw [hBlocks] at hb
  by_contra hNot
  have hMiss : ∀ D ∈ N.pc, ¬(D.slot = C.slot ∧ D.target.root = C.target.root) := by
    intro D hD he
    exact hNot (Or.inr ⟨D, hD, he⟩)
  have hOn := formation_input_on_miss p st s N P C hWF hMiss
  rcases formation_find_old_or_new st.base.blocks N.erase C.target hb with hOld | he
  · have hCompat : activeCompatible st C.target = true := by
      delta activeCompatible
      rw [hF]
      exact Bool.or_eq_true_iff.mpr (Or.inr (Gen.Pure.block_genesis_preceq C.target))
    have hv : pcValid st C = true := by
      change (C.wellFormed && decide (C.target ∈ st.base.blocks) &&
        activeCompatible st C.target) = true
      exact Bool.and_eq_true_iff.mpr ⟨Bool.and_eq_true_iff.mpr
        ⟨hw, decide_eq_true (List.mem_of_find?_eq_some hOld)⟩, hCompat⟩
    have heq := ((assemblePC_some_iff _ C.slot C.target C).mp hc).1
    rw [hOn] at heq
    have hcOld := (assemblePC_some_iff st C.slot C.target C).mpr ⟨heq, hv⟩
    exact hNew (pcsa_formation_collected_identity st _ _ C p.nPos hClosed hOld hcOld)
  · have hs := formation_pc_slot C hw
    exact hNot (Or.inl ⟨(he ▸ hs).symm, congrArg Block.root he⟩)

/-- Every new PC identity from a proposal is covered by root-form carriage. -/
theorem pcsa_formation_admitBlock_root (p : Params) (st : State p.n) (s : Slot)
    (N : NamedProposal p.n) (C : PC p.n)
    (hTree : ∀ b, b ∈ st.base.blocks ↔ ∃ B ∈ st.fg.TF, eraseFG B = b)
    (hClosed : FormationCollected st) (hF : st.fg.F = .genesis)
    (hNew : ¬FormationPCIdentity st C.slot C.target)
    (hm : C ∈ (admitBlock p st s N).pcs) :
    (C.slot = N.erase.slot ∧ C.target.root = N.erase.root) ∨
      ∃ D ∈ N.pc, D.slot = C.slot ∧ D.target.root = C.target.root := by
  delta admitBlock at hm
  split at hm
  · exact (hNew ⟨C, hm, rfl, rfl⟩).elim
  · cases hp : parentFG st N.erase with
    | none => rw [hp] at hm; exact (hNew ⟨C, hm, rfl, rfl⟩).elim
    | some P =>
      rw [hp] at hm
      dsimp only at hm
      split at hm
      · rename_i hAcc
        have hWF : (N.pc.map PC.wellFormed).getD true = true := by
          have hf := hAcc
          change (N.erase != .genesis && decide (N.erase.slot ≤ st.slot p) &&
            !decide (∃ Y ∈ st.fg.TF, Y.root = N.erase.root) &&
            SimplexFG.FGBlock.preceq st.fg.F (fgBlock P N.erase N.rows) &&
            decide (N.erase.parent.slot < N.erase.slot) && s == N.erase.slot &&
            rowsValidForParent p P N.erase.slot N.rows &&
            (N.pc.map PC.wellFormed).getD true && namedContentOk p N) = true at hf
          exact (Bool.and_eq_true_iff.mp (Bool.and_eq_true_iff.mp hf).1).2
        change C ∈ (N.rows.foldl (admitRow p)
          (collectPCs (formationCollectInput p st s N P))).pcs at hm
        exact pcsa_formation_accepted_proposal_root p st s N P C
          hTree hp hAcc hClosed hF hWF hNew hm
      · exact (hNew ⟨C, hm, rfl, rfl⟩).elim

/-- A collected identity does not need another collection call. -/
theorem pcsa_formation_collect_identity_iff (st : State n) (s : Slot) (b : Block)
    (hClosed : FormationCollected st) :
    FormationPCIdentity (collectPCs st) s b ↔ FormationPCIdentity st s b := by
  constructor
  · rintro ⟨C, hm, hs, hb⟩
    by_cases hC : C ∈ st.pcs
    · exact ⟨C, hC, hs, hb⟩
    · obtain ⟨hcand, hfind, hasm⟩ := pcsa_formation_collect_new_origin st C hm hC
      have hi := hClosed C.slot C.target C hcand hfind hasm
      simpa only [hs, hb] using hi
  · rintro ⟨C, hm, hs, hb⟩
    exact ⟨C, collectPCs_pcs_mono st hm, hs, hb⟩

private theorem formation_initial_collected : FormationCollected (initial n) := by
  intro s b C hm
  exact (List.not_mem_nil hm).elim

private theorem formation_row_collected (p : Params) (st : State p.n) (a : RowWire p.n)
    (h : FormationCollected st) : FormationCollected (admitRow p st a) := by
  delta admitRow
  cases (RowWire.decode? a) with
  | none => exact h
  | some x =>
    dsimp only
    split
    · exact h
    · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)

private theorem formation_rows_collected (p : Params) (st : State p.n)
    (as : List (RowWire p.n)) (h : FormationCollected st) :
    FormationCollected (as.foldl (admitRow p) st) := by
  induction as generalizing st with
  | nil => exact h
  | cons a as ih =>
    rw [List.foldl_cons]
    exact ih _ (formation_row_collected p st a h)

private theorem formation_head_collected (p : Params) (st : State p.n) (s : Slot)
    (i : Fin p.n) (r : BlockId) (h : FormationCollected st) :
    FormationCollected (admitHead p st s i r) := by
  delta admitHead GridCO.admitVote
  dsimp only
  split
  · exact h
  · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)

private theorem formation_clockPre_collected (p : Params) (st : State p.n) (t : Time)
    (h : FormationCollected st) : FormationCollected (clockPre p st t) := by
  delta clockPre
  dsimp only
  split <;> split <;> split
  all_goals exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)

private theorem formation_gate_collected (p : Params) (st : State n) (a : Block)
    (cs : List (PC n)) (rank : Option PCRank) (s : Slot) (h : FormationCollected st) :
    FormationCollected (gateFrom p a cs rank st s) := by
  rw [gateFrom_def]
  dsimp only
  cases SA.Root.confirmationFrom p.toParams a (actView st) s with
  | none =>
    exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)
  | some result =>
    dsimp only
    split
    · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)
    · apply List.foldlRecOn
      · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)
      · intro acc ha b _
        apply List.foldlRecOn
        · exact ha
        · intro acc' ha' g _
          exact pcsa_formation_collected_of_frame acc' _ ha' rfl rfl rfl (List.Subset.refl _)

private theorem formation_normalize_collected (st : State n) (h : FormationCollected st) :
    FormationCollected (normalizeS st) := by
  delta normalizeS
  split
  · exact h
  · exact pcsa_formation_collected_of_frame st _ h rfl rfl rfl (List.Subset.refl _)

/-- A tick preserves collection closure. -/
theorem pcsa_formation_clock_collected (p : Params) (st : State p.n) (t : Time)
    (h : FormationCollected st) : FormationCollected (clock p st t) := by
  delta clock
  dsimp only
  split
  · rw [gateStep_def]
    apply formation_normalize_collected
    split
    · exact formation_clockPre_collected p st t h
    · exact formation_gate_collected p _ _ _ _ _ (formation_clockPre_collected p st t h)
  · exact formation_clockPre_collected p st t h

/-- Every handler leaves the supported PC candidates collected. -/
theorem pcsa_formation_process_collected (p : Params) (st : State p.n) (o : Wire p.n)
    (h : FormationCollected st) : FormationCollected (process p st o) := by
  delta process
  cases o.decode with
  | none => exact h
  | some d =>
    cases d with
    | vote s i r => exact formation_head_collected p st s i r h
    | row i body => exact formation_row_collected p st _ h
    | ack s i r => exact pcsa_formation_collect_invariant _
    | pc C =>
      change FormationCollected (admitPC st C)
      delta admitPC
      split
      · exact pcsa_formation_collect_invariant _
      · exact h
    | block s N =>
      change FormationCollected (admitBlock p st s N)
      delta admitBlock
      split
      · exact h
      · cases parentFG st N.erase with
        | none => exact h
        | some P =>
          dsimp only
          split
          · exact formation_rows_collected p _ N.rows (pcsa_formation_collect_invariant _)
          · exact h

/-- Collection closure holds in every reachable store. -/
theorem pcsa_formation_reachable_collected (p : Params) (st : State p.n)
    (h : Reachable p st) : FormationCollected st := by
  induction h with
  | init => exact formation_initial_collected
  | tick t _ ih => exact pcsa_formation_clock_collected p _ t ih
  | deliver o _ ih => exact pcsa_formation_process_collected p _ o ih

end AvailableChain.PCSA

end
